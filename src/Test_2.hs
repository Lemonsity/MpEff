{-# LANGUAGE  TypeOperators, FlexibleContexts, Rank2Types  #-}

import Control.Mp.Eff
import Debug.Trace

-- A @Reader@ effect definition with one operation @ask@ of type @()@ to @a@.
data Reader a e ans = Reader{ ask :: Op () a e ans }

data MyEff e ans = MyEff { myOp :: Op Int Int e ans }

sanityAllDynamic = runEff $
                  handlerExplicit (markerExplicit 100) (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                  performExplicit (markerExplicit 100) myOp 42

sanityAllExplicit = runEff $
                  handler (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                  (\m -> perform myOp 42)
                  
sanity = runEff $
                  handler (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                  (\m -> performExplicit m myOp 42)

localFunction = runEff $
                handler (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                (\m -> do f <- return (\x -> do opWithInput <- perform myOp x
                                                return opWithInput)
                          f 42)

eachHandlesOnce = runEff $
                  handler (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                  (\m_outer -> do f <- return (\x -> handler (MyEff { myOp = operation (\arg k -> k (arg + 100)) }) $
                                                     (\m_inner -> do x' <- perform myOp x
                                                                     return x'))
                                  arg <- perform myOp 42
                                  f arg)

suspendedOperation = runEff $
                     handler (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                     (\m_outer -> do justApply <- return (\f -> handler (MyEff { myOp = operation (\arg k -> k (arg + 100))}) $ 
                                                                (\m_inner -> do fResult <- f ()
                                                                                return fResult))
                                     f <- return (\_ -> perform myOp 42)
                                     justApply f)

explicitHandlerExplicitOperation = runEff $
                                   handlerExplicit (markerExplicit 1) (MyEff { myOp = operation (\arg k -> k (arg + 1)) } ) $
                                   do res <- performExplicit (markerExplicit 1) myOp 42 
                                      return res

explicitHandlerDynamicOperation = runEff $
                                  handlerExplicit (markerExplicit 1) (MyEff { myOp = operation (\arg k -> k (arg + 1)) }) $
                                  do res <- perform myOp 42
                                     return res

mixed = runEff $
        handlerExplicit (markerExplicit 10) (MyEff { myOp = operation (\arg k -> k 1) }) $
        do justApply <- return (\f -> handlerExplicit (markerExplicit 20) (MyEff { myOp = operation (\arg k -> k 100)}) $ 
                                      do fResult <- f ()
                                         return fResult)
           f <- return (\_ -> performExplicit (markerExplicit 10) myOp 42)
           justApply f
