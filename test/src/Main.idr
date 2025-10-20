module Main
import Tests.Mu
import Tests.Exp
import Tests.Omega
main : IO ()
main = do 
    putStrLn "Starting tests..."
    putStrLn "Running Mu tests..."
    muTest
    putStrLn "Running Exp tests..."
    expTest
    putStrLn "Running Omega tests..."
    omegaTest
    putStrLn "All tests completed."
    pure ()
