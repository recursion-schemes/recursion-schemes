import Test.DocTest

main :: IO ()
main = doctest ["-isrc", "-Iinclude", "src/Data/Functor/Foldable.hs"]
