{-# LANGUAGE  TypeOperators, FlexibleContexts, Rank2Types  #-}

import Control.Mp.Eff
import Debug.Trace

-- A @Reader@ effect definition with one operation @ask@ of type @()@ to @a@.
data Reader a e ans = Reader{ ask :: Op () a e ans }

data MyEff e ans = MyEff { myOp :: Op Int Int e ans }

greet :: (Reader String :? e) => Eff e String
greet = do s <- (perform ask ())
           return ("hello " ++ s)

test :: Int
test = runEff $
       handler (Reader{ ask = value "world" }) $  -- @:: Reader String () Int@
       do s <- greet                              -- executes in context @:: `Eff` (Reader String `:*` ()) Int@
          return (length s)

doOpOnInput :: (MyEff :? e) => Int -> Eff e Int
doOpOnInput = \x -> do xAfterOp <- perform myOp x
                       return xAfterOp

callDoOpOnInput = runEff $
                  handler (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                  do doOpOnInput 42

callDoOpOnOpArg = runEff $
                  handler (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                  do arg <- perform myOp 42
                     doOpOnInput arg                     

localFunction = runEff $
                handler (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                do f <- return (\x -> do opWithInput <- perform myOp x
                                         return opWithInput)
                   f 42

localFunctionWithOpArg = runEff $
                         handler (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                         do f <- return (\x -> do opWithInput <- perform myOp x
                                                  return opWithInput)
                            arg <- perform myOp 42
                            f arg 

eachHandlesOnce = runEff $
                  handler (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                  do f <- return (\x -> handler (MyEff { myOp = operation (\arg k -> k (arg + 100)) }) $
                                        do x' <- perform myOp x
                                           return x')
                     arg <- perform myOp 42
                     f arg

suspendedOperation = runEff $
                     handler (MyEff { myOp = operation (\arg k -> k 1) }) $

                     do justApply <- return (\f -> handler (MyEff { myOp = operation (\arg k -> k 100)}) $ 
                                              do fResult <- f ()
                                                 return fResult)
                        f <- return (\_ -> perform myOp 42)
                        justApply f

explicitHandlerExplicitOperation = runEff $
                                   handlerExplicit (markerExplicit 1) (MyEff { myOp = operation (\arg k -> k (arg + 1)) } ) $
                                   do res <- performExplicit (markerExplicit 1) myOp 42 
                                      return res

explicitHandlerDynamicOperation = runEff $
                                  handlerExplicit (markerExplicit 1) (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                                  do res <- perform myOp 42
                                     return res

test' = runEff $
        handlerExplicit (markerExplicit 10) (MyEff { myOp = operation (\arg k -> k 1) }) $

        do justApply <- return (\f -> handlerExplicit (markerExplicit 20) (MyEff { myOp = operation (\arg k -> k 100)}) $ 
                                      do fResult <- f ()
                                         return fResult)
           f <- return (\_ -> performExplicit (markerExplicit 10) myOp 42)
           justApply f
