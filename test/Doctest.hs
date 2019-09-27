import Test.DocTest (doctest)

main :: IO ()
main = doctest
  [ "-fobject-code"
  , "src/Data/Word/Base62.hs"
  ]

