module Main

import Text.PrettyPrint.WL

import Control.Monad.Freer
import Control.Monad.Identity
import Control.Monad.Writer

import AST
import DSL
import Print

ex1 : SMTCommand ()
ex1 = do x' <- declareReal "x" ; let x = toTerm x'
         y' <- declareReal "y" ; let y = toTerm y'
         z' <- declareReal "z" ; let z = toTerm z'
         assert $ (3*x + 2*y - z) `eq` 1
         assert $ (2*x - 2*y + 4*z) `eq` (-2)
         assert $ ((-x) + (d 0.5)*y - z) `eq` 0
         checkSat
         getModel

ex2 : SMTCommand ()
ex2 = do c' <- declareInt "circle"   ; let c = toTermI c'
         t' <- declareInt "triangle" ; let t = toTermI t'
         s' <- declareInt "square"   ; let s = toTermI s'
         assert $ (c + c) `eq` 10
         assert $ (c*s + s) `eq` 12
         assert $ (c*s - t*c) `eq` c
         checkSat
         getModel

ex3 : SMTCommand ()
ex3 = do d' <- declareInt "D" ; let d = toTermI d'
         e' <- declareInt "E" ; let e = toTermI e'
         m' <- declareInt "M" ; let m = toTermI m'
         n' <- declareInt "N" ; let n = toTermI n'
         o' <- declareInt "O" ; let o = toTermI o'
         r' <- declareInt "R" ; let r = toTermI r'
         s' <- declareInt "S" ; let s = toTermI s'
         y' <- declareInt "Y" ; let y = toTermI y'
         assert $ distinct [d, e, m, n, o, r, s, y]
         assert $ (0 `le` d) `and` (d `le` 9)
         assert $ (0 `le` e) `and` (e `le` 9)
         assert $ (0 `le` m) `and` (m `le` 9)
         assert $ (0 `le` n) `and` (n `le` 9)
         assert $ (0 `le` o) `and` (o `le` 9)
         assert $ (0 `le` r) `and` (r `le` 9)
         assert $ (0 `le` s) `and` (s `le` 9)
         assert $ (0 `le` y) `and` (y `le` 9)
         assert $ (1000*s+100*e+10*n+d + 1000*m+100*o+10*r+e) `eq` (10000*m+1000*o+100*n+10*e+y)
         checkSat
         getModel

writeSMT : SMTCommand a -> (fname : String) -> IO ()
writeSMT cmd fname = do Default.writeDoc fname $ ppScript $ renderCommands cmd
                        pure ()

main : IO ()
main = writeSMT ex3 "test3.smt2"
