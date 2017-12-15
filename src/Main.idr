module Main

import Text.PrettyPrint.WL

import AST
import Print

test : List Command
test = [ DeclareConst (MkSymbol "x") (MkSort (MkIdentifier (MkSymbol "Real") []) []) 
       , DeclareConst (MkSymbol "y") (MkSort (MkIdentifier (MkSymbol "Real") []) []) 
       , DeclareConst (MkSymbol "z") (MkSort (MkIdentifier (MkSymbol "Real") []) []) 
       , Assert (FunApp (MkQIdentifier (MkIdentifier (MkSymbol "=") []) Nothing)
                 [ FunApp (MkQIdentifier (MkIdentifier (MkSymbol "-") []) Nothing)
                   [ FunApp (MkQIdentifier (MkIdentifier (MkSymbol "+") []) Nothing)
                     [ FunApp (MkQIdentifier (MkIdentifier (MkSymbol "*") []) Nothing) 
                       [ Lit (Numeral 3)
                       , QI (MkQIdentifier (MkIdentifier (MkSymbol "x") []) Nothing)]
                     , FunApp (MkQIdentifier (MkIdentifier (MkSymbol "*") []) Nothing)
                       [ Lit (Numeral 2)
                       , QI (MkQIdentifier (MkIdentifier (MkSymbol "y") []) Nothing)]]
                   , QI (MkQIdentifier (MkIdentifier (MkSymbol "z") []) Nothing)]
                 , Lit (Numeral 1) ])
       , CheckSat
       , GetModel
       ]
{-
(assert (= (- (+ (* 3 x) (* 2 y)) z) 1))
(assert (= (+ (- (* 2 x) (* 2 y)) (* 4 z)) -2))
(assert (= (- (+ (- 0 x) (* 0.5 y)) z) 0))
-}

main : IO ()
main = do _ <- Default.writeDoc "test.smt2" $ ppScript test
          pure ()
