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