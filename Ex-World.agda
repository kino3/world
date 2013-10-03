----------------------------------------------------
-- A new paradigm for component-based development
-- Examples are written in this paper
----------------------------------------------------
module Ex-World where
open import World
open import Data.String
open import Data.Unit
open import Data.Bool

----------------------------------------------------
-- Example -- simple world 'io' of console applications
----------------------------------------------------

data cio : Set where
  read : cio
  write : String → cio

rio : cio → Set
rio read = String
rio (write _) = ⊤               -- ⊤ is in Data.Unit

io : world
io = cio , rio

----------------------------------------------------
-- Example -- interactive program
-- A program 'pw' over the 'io' world
----------------------------------------------------

pw : String → io ⇒ Bool
pw x = invk (write "enter password:") (λ _ → invk read (λ y → ret (x == y)))


----------------------------------------------------
-- Example -- III. Programming with world maps
----------------------------------------------------
data cio2 : Set where
  scan : cio2
  print : String → cio2

rio2 : cio2 → Set
rio2 scan = String
rio2 (print _) = ⊤               -- ⊤ is in Data.Unit

io2 : world
io2 = cio2 , rio2

-- example of world-map
iomap : io ⊸ io2
iomap scan = invk read ret
iomap (print x) = invk (write x) ret

-- terminal-world?
data term-com : Set where
  hoge : term-com

term-res : term-com → Set
term-res hoge = ⊤

term-world : world
term-world = term-com , term-res

term-wmap : io ⊸ term-world
term-wmap hoge = ret tt

-- lifting sample?
test : io ⇒ String
test = lift iomap (invk scan ret)

-- password test
testmap : term-world ⊸ io
testmap read = ret "hello"
testmap (write _) = ret tt

lifttest : term-world ⇒ Bool
lifttest = lift testmap (pw "hogehoge")


----------------------------------------------------
-- Event-driven programs
----------------------------------------------------



----------------------------------------------------
-- Session state
----------------------------------------------------
{-
data challenge : Set where
  * : challenge

data cookie : Set where
  * : cookie

data session : world where
  * : session

data service : world where


ss : {a : Set} → cookie → (session ⇒ a) → (service ⇒ a)
ss c (ret a) = ret a
-}