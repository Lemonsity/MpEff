{-# LANGUAGE  TypeOperators,            -- h :* e                     (looks nice but not required)
              ConstraintKinds,          -- type (h ?: e) = In h e     (looks nice but not required)
              FlexibleInstances,        -- instance Sub () e          (non type variable in head)
              FlexibleContexts,         -- (State Int ?: e) => ...    (non type variable argument)
              DataKinds, TypeFamilies,  -- type family HEqual h h' :: Bool
              UndecidableInstances,     -- InEq (HEqual h h') h h' e => ... (duplicate instance variable)
              ScopedTypeVariables,
              GADTs,
              MultiParamTypeClasses,
              Rank2Types,
              RankNTypes,
              KindSignatures
#-}
{-|
Description : Efficient effect handlers based on Evidence Passing Semantics
Copyright   : (c) 2021, Ningning Xie, Daan Leijen
License     : MIT
Maintainer  : xnning@hku.hk; daan@microsoft.com
Stability   : Experimental

Efficient effect handlers based on Evidence passing semantics. The implementation
is based on /"Generalized Evidence Passing for Effect Handlers"/, Ningning Xie and Daan Leijen, 2021 [(pdf)](https://www.microsoft.com/en-us/research/publication/generalized-evidence-passing-for-effect-handlers/),
The implementation is closely based on the [Ev.Eff](https://hackage.haskell.org/package/eveff) 
library described in detail in /"Effect Handlers in Haskell, Evidently"/, Ningning Xie and Daan Leijen, Haskell 2020 [(pdf)](https://www.microsoft.com/en-us/research/publication/effect-handlers-in-haskell-evidently).
The _Mp.Eff_ and _Ev.Eff_ libraries expose the exact same interface, but
the _Mp.Eff_ library can express full effect handler semantics, including non-scoped resumptions --
it is slightly slower though (see the 2021 paper for benchmarks and a detailed comparison).

An example of defining and using a @Reader@ effect:

@
\{\-\# LANGUAGE  TypeOperators, FlexibleContexts, Rank2Types  \#\-\}
import Control.Mp.Eff

-- A @Reader@ effect definition with one operation @ask@ of type @()@ to @a@.
data Reader a e ans = Reader{ ask :: `Op` () a e ans }

greet :: (Reader String `:?` e) => `Eff` e String
greet = do s <- `perform` ask ()
           return ("hello " ++ s)

test :: String
test = `runEff` $
       `handler` (Reader{ ask = `value` "world" }) $  -- @:: Reader String () Int@
       do s <- greet                              -- executes in context @:: `Eff` (Reader String `:*` ()) Int@
          return (length s)
@

Enjoy,

Ningning Xie and Daan Leijen,  Mar 2021.

-}
module Control.Mp.Eff(
              Marker
            , markerExplicit
            , handlerExplicit
            , performExplicit
  
            -- * Effect monad
            , Eff
            , runEff          -- :: Eff () a -> a

            -- * Effect context
            , (:?)            -- h :? e,  is h in e?
            , (:*)            -- h :* e,  cons h in front of e
            -- , In           -- alias for :?

            -- * Perform and Handlers
            , perform         -- :: (h :? e) => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
            , handler         -- :: h e ans -> Eff (h :* e) ans -> Eff e ans
            , handlerRet      -- :: (ans -> b) -> h e b -> Eff (h :* e) ans -> Eff e b
            , handlerHide     -- :: h (h' :* e) ans -> Eff (h :* e) ans -> Eff (h' :* e) ans
            , mask            -- :: Eff e ans -> Eff (h :* e) ans

            -- * Defining operations
            , Op
            , value           -- :: a -> Op () a e ans
            , function        -- :: (a -> Eff e b) -> Op a b e ans
            , except          -- :: (a -> Eff e ans) -> Op a b e ans
            , operation       -- :: (a -> (b -> Eff e ans)) -> Op a b e ans

            -- * Local state
            , Local           -- Local a e ans

            , local           -- :: a -> Eff (Local a :* e) ans -> Eff e ans
            , localRet        -- :: a -> (ans -> a -> b) -> Eff (Local a :* e) ans -> Eff e b
            , handlerLocal    -- :: a -> h (Local a :* e) ans -> Eff (h :* e) ans -> Eff e ans
            , handlerLocalRet -- :: a -> (ans -> a -> b) -> h (Local a :* e) b -> Eff (h :* e) ans -> Eff e b

            , lget            -- :: (Local a :? e) => Eff e a
            , lput            -- :: (Local a :? e) => a -> Eff e ()
            , lmodify         -- :: (Local a :? e) => (a -> a) -> Eff e ()

            , localGet        -- :: Eff (Local a :* e) a
            , localPut        -- :: a -> Eff (Local a :* e) ()
            , localModify     -- :: (a -> a) -> Eff (Local a :* e) a

            ) where

import Prelude hiding (read,flip)
import Control.Monad( ap, liftM )
import Data.Type.Equality( (:~:)( Refl ) )
import Control.Monad.Primitive

-------------------------------------------------------
-- Assume some way to generate a fresh prompt marker
-- associated with specific effect and answer type.
-------------------------------------------------------
import Unsafe.Coerce     (unsafeCoerce)
import System.IO.Unsafe ( unsafePerformIO )
import Data.IORef

import Debug.Trace

data Nat = Z | S Nat deriving (Show)

data TNat :: Nat -> * where
  CZ :: TNat 'Z
  CS :: TNat n -> TNat ('S n) deriving (Show)

-- an abstract marker
data Marker (h:: * -> * -> *) m e a where
  Marker :: !Integer -> TNat n -> Marker h (TNat n) e a 

instance Show (Marker h e a) where
  show (Marker i) = show i

-- if markers match, their types are the same
mmatch :: Marker h m e a -> Marker h' m' e' b -> Maybe ((h e a, a, e) :~: (h' e' b, b, e'))
mmatch (Marker i _) (Marker j _) | i == j  = Just (unsafeCoerce Refl)
mmatch _ _ = Nothing

markerExplicit :: TNat n -> Marker h (TNat n) e a
markerExplicit m = Marker m

-------------------------------------------------------
-- The handler context
-------------------------------------------------------

data MyList (h :: * -> * -> *) (m :: *) e

data Context e where
  CCons :: !(Marker h m e' ans) -> !(h e' ans) -> !(ContextT e e') -> !(Context e) -> Context (MyList h m e)
  CNil  :: Context ()

data ContextT e e' where
  CTCons :: !(Marker h m e' ans) -> !(h e' ans) -> !(ContextT e e') -> ContextT e (MyList h m e)
  CTId   :: ContextT e e
  -- CTComp :: ContextT e'' e' -> ContextT e e'' -> ContextT e e'
  -- CTFun :: !(Context e -> Context e') -> ContextT e e'

-- apply a context transformer
applyT :: ContextT e e' -> Context e -> Context e'
applyT (CTCons m h g) ctx = CCons m h g ctx
applyT (CTId) ctx         = ctx
--applyT (CTComp c1 c2) ctx = applyT c1 (applyT c2 ctx)
--applyT (CTFun f) ctx = f ctx

-- the tail of a context
ctail :: Context (MyList h m e) -> Context e
ctail (CCons _ _ _ ctx)   = ctx

-------------------------------------------------------
-- The Multi Prompt control monad
-- ans: the answer type, i.e. the type of the handler/prompt context.
-- e' : the answer effect, i.e. the effect in the handler/prompt context.
-- b  : the result type of the operation
-------------------------------------------------------
data Ctl e a = Pure { result :: !a }
             | forall h b e' ans m .
               Control{ marker :: Marker h m e' ans,                   -- prompt marker to yield to (in type context `::ans`)
                        op     :: !((b -> Eff e' ans) -> Eff e' ans),  -- the final action, just needs the resumption (:: b -> Eff e' ans) to be evaluated.
                        cont   :: !(b -> Eff e a) }                    -- the (partially) build up resumption; (b -> Eff e a) :~: (b -> Eff e' ans)` by the time we reach the prompt


newtype Eff e a = Eff { unEff :: Context e -> Ctl e a }

{-# INLINE lift #-}
lift :: Ctl e a -> Eff e a
lift ctl = Eff (\ctx -> ctl)

{-# INLINE ctxMap #-}
ctxMap :: (Context e' -> Context e) -> Eff e a -> Eff e' a
ctxMap f eff = Eff $
               traceShow "ctxMap: Storing new unEff function" $
               (\ctx -> ctxMapCtl f $
                        traceShow "ctxMap: Ran effectful computation, in different context" $
                        unEff eff (f ctx))

{-# INLINE ctxMapCtl #-}
ctxMapCtl :: (Context e' -> Context e) -> Ctl e a -> Ctl e' a
ctxMapCtl f (Pure x) = Pure x
ctxMapCtl f (Control m op cont) = Control m op (\b -> ctxMap f (cont b))

instance Functor (Eff e) where
  fmap  = liftM
instance Applicative (Eff e) where
  pure  = return
  (<*>) = ap
instance Monad (Eff e) where
  return x   = Eff (\evv -> Pure x)
  (>>=)      = bind

-- start yielding (with an initially empty continuation)
{-# INLINE yield #-}
yield :: Marker h m e ans -> ((b -> Eff e ans) -> Eff e ans) -> Eff e' b
yield m op  = Eff $
              traceShow "yield: Storing new unEff function" $
              (\ctx -> Control m op pure)

{-# INLINE kcompose #-}
kcompose :: (b -> Eff e c) -> (a -> Eff e b) -> a -> Eff e c      -- Kleisli composition
kcompose g f x =
  case f x of
    -- bind (f x) g
    Eff eff -> Eff $
               traceShow "kcompose: Storing new unEff function" $
               (\ctx -> case traceShow "kcompose: Ran first part of computation" $
                             eff ctx of
                          Pure x -> traceShow "kcompose: Run the composed composed computation" $
                                    unEff (g x) ctx
                          Control m op cont -> Control m op (g `kcompose` cont))

{-# INLINE bind #-}
bind :: Eff e a -> (a -> Eff e b) -> Eff e b
bind (Eff eff) f
  = Eff $
    traceShow "bind: Storing new unEff function" $
    (\ctx -> case traceShow "Eff bind: Composed continuation is executed" $
                  traceShow "Eff bind: Run the 'first' part" $
                  eff ctx of
               Pure x            -> traceShow "Eff bind: Running the new effectful computation" $
                                    unEff (f x) ctx
               Control m op cont -> traceShow "Eff bind: Composing continuation" $
                                    Control m op (f `kcompose` cont))  -- keep yielding with an extended continuation

instance Functor (Ctl e) where
  fmap  = liftM
instance Applicative (Ctl e) where
  pure  = return
  (<*>) = ap
instance Monad (Ctl e) where
  return x      = Pure x
  Pure x >>= f  = f x
  (Control m op cont) >>= f
    = traceShow ("Ctl >>=: Ctl's bind is expanding a operation call of marker:", m) $
      Control m op (f `kcompose2` cont)

kcompose2 :: (b -> Ctl e c) -> (a -> Eff e b) -> a -> Eff e c
kcompose2 g f x
  = Eff $
    traceShow "kcompose2: Storing new unEff function" $
    (\ctx -> case unEff (f x) ctx of
               Pure x -> g x
               Control m op cont -> Control m op (g `kcompose2` cont))


-- use a prompt with a unique marker (and handle yields to it)
{-# INLINE prompt #-}
prompt :: Marker h m e ans -> h e ans -> Eff (MyList h m e) ans -> Eff e ans
prompt m h (Eff eff) =
  traceShow "prompt: Calling, which should generate new computation" $
  Eff $
  traceShow "bind: Storing new unEff function" $
  (\ctx ->
     case traceShow "prompt: Running the given effectful computation" $
          (eff (CCons m h CTId ctx)) of                    -- add handler to the context
       Pure x -> traceShow ("Case evaluate to Pure, with marker:", m) $
                 Pure x
       Control n op cont -> traceShow ("prompt: Case evaluate to Control, with marker:", m) $
                            traceShow ("prompt: Case evaluate to Control, the control is referring to marker:", n) $
                            let cont' x = traceShow "prompt: New continuation genearted in prompt" $
                                          prompt m h (cont x) -- extend the continuation with our own prompt
                            in case mmatch m n of
                              Nothing   -> traceShow "prompt: Markers did not match" $
                                           Control n op cont'         -- keep yielding (but with the extended continuation)
                              Just Refl -> traceShow "prompt: Markers matched" $
                                           unEff (op cont') ctx)   -- found our prompt, invoke `op` (under the context `ctx`).
                                           -- Note: `Refl` proves `a ~ ans` and `e ~ e'` (the existential `ans,e'` in Control)

-- A handler with explicit id
{-# INLINE handlerExplicit #-}
handlerExplicit :: Marker h m e ans -> h e ans -> Eff (MyList h m e) ans -> Eff e ans
handlerExplicit marker handlerImpl action
  = prompt marker handlerImpl action

-- Run a control monad
runEff :: Eff () a -> a
runEff (Eff ctxToComp) = case ctxToComp CNil of
                   Pure x -> x
                   Control _ _ _ -> error "Unhandled operation"  -- can never happen

---------------------------------------------------------
--
---------------------------------------------------------

type h :? e = In h e

data SubContext h = forall m e. SubContext !(Context (MyList h m e))

class In h e where
  subContext :: Context e -> SubContext h

instance (InEq (HEqual h h') h h' ctx) => In h (MyList h' m ctx)  where
  subContext = subContextEq

type family HEqual (h :: * -> * -> *) (h' :: * -> * -> *) :: Bool where
  HEqual h h  = 'True
  HEqual h h' = 'False

class (iseq ~ HEqual h h') => InEq iseq h h' e  where
  subContextEq :: Context (h' :* e) -> SubContext h

instance (h ~ h') => InEq 'True h h' e where
  subContextEq ctx = SubContext ctx

instance ('False ~ HEqual h h', In h e) => InEq 'False h h' e where
  subContextEq ctx = subContext (ctail ctx)


{-# INLINE withSubContext #-}
withSubContext :: (In h e) => (SubContext h -> Eff e a) -> Eff e a
withSubContext action
  = do ctx <- Eff Pure
       action (subContext ctx)


------------------------------------
-- Operations
-------------------------------------

-- | The abstract type of operations of type @a@ to @b@, for a handler
-- defined in an effect context @e@ and answer type @ans@.
data Op a b e ans = Op { applyOp:: !(forall h e'. In h e' => Marker h e ans -> Context e -> a -> Eff e' b) }


-- Given evidence and an operation selector, perform the operation
{-# INLINE perform #-}
perform :: In h e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
perform selectOp x
  = trace "perform: Calling perform" $ withSubContext $ \(SubContext (CCons m h transform ctx)) ->
                                                          traceShow ("handler: Got handler with marker:", m) $
                                                          (applyOp (selectOp h)) m (applyT transform ctx) x

getHandlerByMarker :: Marker h e ans -> Context e' -> (Marker h e ans, h e ans)
getHandlerByMarker _ CNil = error "getHandlerByMarker: No handler found"
getHandlerByMarker m (CCons m' hImpl trans subCtx) =
  case mmatch m m' of
    Nothing -> getHandlerByMarker m subCtx
    Just Refl -> (m', hImpl)

performExplicit :: In h e => Marker h e ans -> (forall e' ans . (h e' ans) -> Op a b e' ans) -> a -> Eff e b
performExplicit m selectOp x
  = Eff $
    (\ctx -> let (m', hImpl) = getHandlerByMarker m ctx
                 newCtxToComp = (applyOp (selectOp hImpl)) m' ctx x
             in (unEff newCtxToComp) ctx)

operation :: (a -> (b -> Eff e ans) -> Eff e ans) -> Op a b e ans
operation f = Op (\m ctx x -> yield m (\ctlk -> f x ctlk))
