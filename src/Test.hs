{-# LANGUAGE  TypeOperators, FlexibleContexts, Rank2Types  #-}

import Control.Mp.Eff
import Debug.Trace

-- A @Reader@ effect definition with one operation @ask@ of type @()@ to @a@.
data Reader a e ans = Reader{ ask :: Op () a e ans }

data MyEff e ans = MyEff { op1 :: Op Int Int e ans }

greet :: (Reader String :? e) => Eff e String
greet = do s <- (perform ask ())
           return ("hello " ++ s)

test :: Int
test = runEff $
       handler (Reader{ ask = value "world" }) $  -- @:: Reader String () Int@
       do s <- greet                              -- executes in context @:: `Eff` (Reader String `:*` ()) Int@
          return (length s)

g :: (MyEff :? e) => Int -> Eff e Int
g = \x -> do xAdd1 <- perform op1 x
             return xAdd1

test2 = runEff $
        handler (MyEff { op1 = operation (\arg k -> k (arg + 1)) }) $
        do arg <- perform op1 10
           g arg

test3 = runEff $
        handler (MyEff { op1 = operation (\arg k -> k (arg + 1)) }) $
        do f <- return (\x -> do xAdd1 <- perform op1 x
                                 return xAdd1)
           arg <- perform op1 10
           f arg

test4 = runEff $
        handler (MyEff { op1 = operation (\arg k -> k (arg + 1)) }) $
        do f <- return (\x -> handler (MyEff { op1 = operation (\arg k -> k (arg + 10)) }) $
                              do x' <- perform op1 x
                                 return x')
           arg <- perform op1 0
           f arg

test5 = runEff $
        handler (MyEff { op1 = operation (\arg k -> k 0) }) $
        -- justApply = \f -> handle { f () } with { op1 ... }
        do justApply <- return (\f -> handler (MyEff { op1 = operation (\arg k -> k 10)}) $ 
                                      do fResult <- f ()
                                         return fResult)
            -- f = \_ -> perform op1 0
           f <- return (\_ -> perform op1 0)
           justApply f

test6 = runEff $
        handlerExplicit (markerExplicit 10) (Reader { ask = value "hello" } ) $
        do s <- (perform ask () :: Eff (Reader [Char] :* ()) [Char])
           return s


test7 = runEff $
        handler (Reader { ask = value "World" }) $
        do f <- return (\_ -> do result <- (perform ask () :: Eff (Reader [Char] :* ()) [Char])
                                 return result)
           f ()
