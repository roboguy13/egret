f :: Bool -> Bool
f x = x

g :: Bool -> Bool
g x = case x of { True -> x; False -> x }

main :: IO ()
main = do
  let x = True
      y = False

      z = True
      w = False

      a = f x
      b = g y

  print (f z)
  print (g w)
