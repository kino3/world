----------------------------------------------------
-- A new paradigm for component-based development --
--                        2012 Johan G. Granström --
----------------------------------------------------

module World where


infix  10 _≐_
infixl 50 _>>=_
infix  60 ret
infix  60 invk


--------------------------
-- I. THE MONAD OF A WORLD
--------------------------

-- The notion of world is defined as follows by Hancock and Setzer.
-- Definition of world
open import Level hiding (lift)

record World (l : Level) : Set (suc l) where
  constructor _,_
  field
    C : Set l                    -- the set of commands
    R : C → Set l                -- the set of responses indexed by commands
-- todo: always l1 == l2?

-- the set of commands of w
∣_∣ : {l1 : Level} → World l1 → Set l1
∣ C , R ∣ = C

-- the set of responses to a command c
_at_ : {l1 : Level} → (w : World l1) → World.C w → Set l1
(C , R) at c = R c --R c

-- Definition of interactive program
data _⇒_ {l1 : Level} (w : World l1) (A : Set l1) : Set l1  where -- 
  ret  : A → (w ⇒ A)
  invk : (c : ∣ w ∣) → ((w at c) → (w ⇒ A)) → (w ⇒ A)


-- The bind operation
_>>=_ : {l1 : Level} {A B : Set l1} {w : World l1} → (w ⇒ A) → (A → (w ⇒ B)) → (w ⇒ B)
(ret a)    >>= f = f a                      -- : w ⇒ B
(invk c t) >>= f = invk c (λ x → t x >>= f) -- : w ⇒ B


--------------------------------------------
-- II. THE CATEGORY OF WORLDS AND WORLD MAPS
--------------------------------------------

-- Definition of world map
_⊸_ : {l : Level} → World l → World l → Set l -- multimap = ⊸
w1 ⊸ w2 = (x : ∣ w2 ∣) → w1 ⇒ (w2 at x)
-- TODO: Could we combine "bind" and "invoke" ?

-- (m : w1 ⊸ w2)
-- (m c) , where c : / w2 / is an interactive program over the world w1
-- giving as result an element of the set (w2 at c)

-- Lifting
lift : {l : Level} {w1 w2 : World l} {A : Set l} → (w1 ⊸ w2) → (w2 ⇒ A) → (w1 ⇒ A)
lift m (ret a) = ret a
lift m (invk c t) = m c >>= (λ x → lift m (t x))

  -- It can be used to interpret programs over w2 in terms of programs over w1.

-- Identity maps (proof is in Lemma 3)
id : {l : Level} (w : World l) → (w ⊸ w)
id w c = invk c ret

-- Composition of world maps
_⁏_ : {l : Level} {w1 w2 w3 : World l} (m : w1 ⊸ w2) → (n : w2 ⊸ w3) → (w1 ⊸ w3)
(m ⁏ n) c = lift m (n c) -- : w1 ⇒ w3 at c
-- ⁏ = reversed semicolon

--------------------------
-- Equality
--------------------------

-- Equality between programs
data _≐_ {l : Level} {w : World l} {A : Set l} : (w ⇒ A) → (w ⇒ A) → Set l where
  rret : (a : A) → (ret a) ≐ (ret a)
  rinvk : {c : ∣ w ∣} → (s t : w at c → (w ⇒ A)) → ((x : w at c) → s x ≐ t x) → invk c s ≐ invk c t

-- Equality between world maps ( ≗ = C-x 8 ret 2257)
_≗_ : {l : Level} {w1 w2 : World l} → (w1 ⊸ w2) → (w1 ⊸ w2) → Set l
_≗_ {l} {w1} {w2} m n = (x : ∣ w2 ∣) → m x ≐ n x 

{-
--- families of worlds
record Ω (A : Set) : Set₁ where
  constructor _,_
  field
    CΩ : A → Set
    RΩ : (x : A) → CΩ x → Set

-}
