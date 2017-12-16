module Main

import Text.PrettyPrint.WL

import AST
import DSL
import Print

test : List Command
test = [ declareReal "x"
       , declareReal "y"
       , declareReal "z"
       , assert $ app "=" [ app "-" [ app "+" [ app "*" [ num 3, var "x" ]
                                              , app "*" [ num 2, var "y" ]]
                                    , var "z" ]
                          , num 1 ]
       , assert $ app "=" [ app "+" [ app "-" [ app "*" [ num 2, var "x" ]
                                              , app "*" [ num 2, var "y" ]]
                                    , app "*" [ num 4, var "z" ] ]
                          , num (-2) ]
       , assert $ app "=" [ app "-" [ app "+" [ app "-" [ num 0, var "x" ]
                                              , app "*" [ dec 0.5, var "y" ]]
                                    , var "z" ]
                          , num 0 ]
       , checkSat
       , getModel
       ]

main : IO ()
main = do _ <- Default.writeDoc "test.smt2" $ ppScript test
          pure ()
