open import System.IO using (_>>_ ; putStr ; commit)

module HelloWorld  where

main = putStr "Hello, World\n" >> commit
