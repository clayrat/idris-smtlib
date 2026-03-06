module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner [ "Lib tests" `atDir` "lib"
                    , "Backend tests" `atDir` "backend"
                    , "Parse tests" `atDir` "parse"
                    ]
