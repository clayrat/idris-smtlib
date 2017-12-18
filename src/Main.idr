module Main

import System
import Text.PrettyPrint.WL

import Control.Monad.Freer
import Control.Monad.Identity
import Control.Monad.Writer

import AST
import DSL
import Print

ex1 : SMTCommand ()
ex1 = do ds' <- traverse declareReal ["x", "y", "z"]
         case map toTerm ds' of 
           [x, y, z] => 
             do assert $ (3*x + 2*y - z) `eq` 1
                assert $ (2*x - 2*y + 4*z) `eq` (-2)
                assert $ ((-x) + (d 0.5)*y - z) `eq` 0
                checkSat
                getModel
           _ => Pure ()

ex2 : SMTCommand ()
ex2 = do ds' <- traverse declareInt ["circle", "triangle", "square"]
         case map toTermI ds' of 
           [c, t, s] => 
             do assert $ (c + c) `eq` 10
                assert $ (c*s + s) `eq` 12
                assert $ (c*s - t*c) `eq` c
                checkSat
                getModel
           _ => Pure ()

ex3 : SMTCommand ()
ex3 = do ds' <- traverse declareInt ["D", "E", "M", "N", "O", "R", "S", "Y"] 
         let ds = map toTermI ds'
         let isDigit = \x => (0 `le` x) `and` (x `le` 9)
         let construct = \xs : List Term => sum $ zipWith (*) (reverse xs) $ map fromInteger $ take (length xs) (iterate (*10) 1)
         assert $ distinct ds
         traverse_ (assert . isDigit) ds
         case ds of 
           [d,e,m,n,o,r,s,y] => 
             do let send  = construct [s,e,n,d]
                let more  = construct [m,o,r,e]
                let money = construct [m,o,n,e,y]
                assert $ (send + more) `eq` money
                checkSat
                getModel    
           _ => Pure ()

ex4 : SMTCommand ()
ex4 = do ds' <- traverse declareInt ["A", "I", "L", "N", "O", "R", "S", "T", "V"]
         let ds = map toTermI ds'
         let isDigit = \x => (0 `le` x) `and` (x `le` 9)
         let construct = \xs : List Term => sum $ zipWith (*) (reverse xs) $ map fromInteger $ take (length xs) (iterate (*10) 1)         
         assert $ distinct ds
         traverse_ (assert . isDigit) ds
         case ds of 
           [a,i,l,n,o,r,s,t,v] =>
             do let violin = construct [v,i,o,l,i,n]               
                let viola  = construct [v,i,o,l,a]               
                let sonata = construct [s,o,n,a,t,a]               
                let trio   = construct [t,r,i,o]               
                assert $ (violin + violin + viola) `eq` (trio + sonata)
                checkSat
                getModel
           _ => Pure ()
               
         
ex5 : SMTCommand ()
ex5 = do ds' <- traverse declareInt ["H", "E", "L", "O", "W", "R", "D"]
         let ds = map toTermI ds'
         let isPos = \x => (1 `le` x) `and` (x `le` 9) 
         assert $ distinct ds
         traverse_ (assert . isPos) ds
         case ds of  
           [h, e, l, o, w, r, d] =>
             do assert $ (h + e + l + l + o) `eq` 25
                assert $ (w + o + r + l + d) `eq` 25
                checkSat
                getModel         
           _ => Pure ()

writeSMT : SMTCommand a -> (fname : String) -> IO ()
writeSMT cmd fname = do Default.writeDoc fname $ ppScript $ renderCommands cmd
                        pure ()

execZ3 : (infile, outfile : String) -> IO Int
execZ3 infile outfile = system $ "z3 -smt2 " ++ infile ++ " > " ++ outfile

main : IO ()
main = do let inf = "test4.smt2"
          let outf = "out.smt2"
          writeSMT ex4 inf
          i <- execZ3 inf outf
          printLn i
          eos <- readFile outf
          case eos of 
            Left err => printLn err
            Right str => for_ (lines str) putStrLn
