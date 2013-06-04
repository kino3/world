----------------------------------------------------
-- A new paradigm for component-based development
-- Proofs are written in this file
----------------------------------------------------

module Proof-World where
open import World
import Eq

-- Proposition 1: Program equality is an equivalence relation.
-- equiv = refl & sym & trans
refl : {w : world} {A : Set} {wa : w ⇒ A} → wa ≐ wa
refl {A} {w} {ret a} = rret a
refl {A} {w} {invk c t} = rinvk t t (λ x → refl {- t x -})

sym : {w : world} {A : Set} {wa wb : w ⇒ A} → wa ≐ wb → wb ≐ wa
sym {w} {A} {ret a} {ret .a} (rret .a) = rret a
sym {w} {A} {ret a} {invk c t} ()
sym {w} {A} {invk c s} {ret a} ()
sym {w} {A} {invk c s} {invk .c t} (rinvk .s .t h)
  = rinvk t s (λ x → sym {w} {A} {s x} {t x} (h x))

trans : {A : Set} {w : world} {wa wb wc : w ⇒ A} → wa ≐ wb → wb ≐ wc → wa ≐ wc
trans {A} {w} {ret a} {ret .a} {ret .a} (rret .a) (rret .a) = rret a
trans {A} {w} {ret _} {ret _} {invk _ _} _ ()
trans {A} {w} {ret _} {invk _ _} {_} () _
trans {A} {w} {invk _ _} {ret _} {_} () _
trans {A} {w} {invk _ _} {invk _ _} {ret _} _ ()
trans {A} {w} {invk c t0} {invk .c t1} {invk .c t2} (rinvk .t0 .t1 h0) (rinvk .t1 .t2 h1)
  = rinvk t0 t2 (λ x → trans {A} {w}  {t0 x} {t1 x} {t2 x} (h0 x) (h1 x))

------------------------------------------------------------------------------------
-- lemma -- congruence of bind(>>=)

bind-cong : {w : world} {A B : Set} {f g : A → w ⇒ B}
      → {p q : w ⇒ A} → p ≐ q → ((a0 : A) → f a0 ≐ g a0)
      → (p >>= f) ≐ (q >>= g)
bind-cong {w} {A} {B} {f} {g} {ret a} {ret .a} (rret .a) f≐g = f≐g a
bind-cong {w} {A} {B} {f} {g} {invk c s} {invk .c t} (rinvk {.c} .s .t s≐t) f≐g
      = rinvk (λ x → s x >>= f) (λ x → t x >>= g)
              (λ x → bind-cong {w} {A} {B} {f} {g} {s x} {t x} (s≐t x) f≐g)
bind-cong {w} {A} {B} {f} {g} {ret _} {invk _ _} () _
bind-cong {w} {A} {B} {f} {g} {invk _ _} {ret _} () _
------------------------------------------------------------------------------------

-- Theorem 2: (w ⇒) is a monad satisfying the monad laws up to program equality.

-- ηA* = idTA
monad-right-id : {w : world} {A : Set} (p : w ⇒ A) → p >>= ret ≐ p
monad-right-id (ret a) = rret a
monad-right-id (invk c t) = rinvk (λ x → t x >>= ret) t (λ x → monad-right-id (t x))

-- ηA;f* = f
monad-left-id : {w : world} {A B : Set} {f : A → (w ⇒ B)} → (a : A) → ret a >>= f ≐ f a
monad-left-id = λ a → refl

-- (f* ; g*) = (f ; g*)*
monad-assoc : {w : world} {A B C : Set}
  → (f : A → (w ⇒ B)) → (g : B → (w ⇒ C)) → (p : w ⇒ A)
  → (p >>= f) >>= g ≐ p >>= (λ x → f x >>= g)
monad-assoc f g (ret a) = refl
monad-assoc {w} {A} {B} {C} f g (invk c t)
  = rinvk (λ x → t x >>= f >>= g)
          (λ x → t x >>= (λ y → f y >>= g))
          (λ x → monad-assoc f g (t x))

-- Lemma 3: The identity map id w : w ⊸ w

-- TODO: use another equality.  ≗ is easy to understand.

lemma3-1 : {w1 w2 : world} {c : / w2 /} {m : w1 ⊸ w2} → (id w1 ⁏ m) c ≐ (m c)
lemma3-1 {w1} {w2} {c} {m} = lemma (m c)
  where
    lemma : {w : world} {A : Set} (prog : w ⇒ A) → (lift (id w) prog) ≐ prog
    lemma {w} {A} (ret a) = rret a
    lemma {w} {A} (invk c t) =
      let
        open Eq {_} {w ⇒ A} _≐_ refl sym trans
      in
        ∵ (lift (id w) (invk c t))
                ≈ id w c >>= (λ x → lift (id w) (t x)) by refl
                ≈ id w c >>= (λ x → t x)     by bind-cong {f = (λ x → lift (id w) (t x))}
                                                         {g = λ x → t x}
                                                         {p = id w c} refl (λ a0 → lemma (t a0))
                ≈ id w c >>= t                 by rinvk t t (λ x → refl)
                ≈ invk c ret >>= t             by rinvk t t (λ x → refl)
                ≈ invk c (λ x → ret x >>= t) by rinvk t t (λ x → refl)
                ≈ invk c (λ x → t x)         by rinvk t t (λ x → refl)
                ≈ invk c t                     by rinvk t t (λ x → refl)
  
lemma3-2 : {w1 w2 : world} {A : Set} {n : w1 ⊸ w2} {c : / w2 /}
                                                          → (n ⁏ id w2) c ≐ n c
lemma3-2 {w1} {w2} {A} {n} {c} = 
  let
    open Eq {_} {w1 ⇒ (w2 at c)} _≐_ refl sym trans
  in
    ∵ ((n ⁏ (id w2)) c) ≈ lift n (id w2 c)                 by refl
                         ≈ lift n (invk c ret)              by refl
                         ≈ n c >>= (λ x → lift n (ret x)) by refl
                         ≈ n c >>= ret                      by refl
                         ≈ n c                              by monad-right-id (n c)

-- Lemma 4: Composition of world maps is associative.
lemma4 : {w1 w2 w3 w4 : world} {f : w1 ⊸ w2} {g : w2 ⊸ w3} {h : w3 ⊸ w4} {c : / w4 /} {A : Set}
  → ((f ⁏ g) ⁏ h) c ≐ (f ⁏ (g ⁏ h)) c
lemma4 {w1} {w2} {w3} {w4} {f} {g} {h} {c} {A} = 
  let
    open Eq {_} {w1 ⇒ _} _≐_ refl sym trans
  in
    ∵ (((f ⁏ g) ⁏ h) c) ≈ lift (f ⁏ g) (h c) by refl
                         ≈ lift f (lift g (h c)) by lemma4-1 (h c)
                         ≈ (f ⁏ (g ⁏ h)) c by refl
  where
    lemma4-1 : (p : w3 ⇒ (w4 at c)) → lift (f ⁏ g) p ≐ lift f (lift g p)
    lemma4-1 (ret a) =
      let
        open Eq {_} {w1 ⇒ _} _≐_ refl sym trans
      in
        ∵ (lift (f ⁏ g) (ret a)) ≈ ret a by refl
                                  ≈ lift f (ret a) by refl
                                  ≈ (lift f (lift g (ret a))) by refl
    lemma4-1 (invk c d) = 
      let
        open Eq {_} {w1 ⇒ _} _≐_ refl sym trans
      in
        ∵ (lift (f ⁏ g) (invk c d))
        ≈ lift f (g c) >>= (λ x → lift (f ⁏ g) (d x)) by refl
        ≈ lift f (g c >>= (λ x → lift g (d x))) by prop (g c)
        ≈ lift f (lift g (invk c d)) by refl
      where
        -- induction on (g c)
        prop : (m : w2 ⇒ (w3 at c)) → (lift f m >>= (λ x → lift (f ⁏ g) (d x)))
                                      ≐ (lift f (m >>= λ x → lift g (d x)))
        prop (ret a) = 
          let
            open Eq {_} {w1 ⇒ _} _≐_ refl sym trans
          in
            ∵ (lift f (ret a) >>= (λ x → lift (f ⁏ g) (d x)))
            ≈ (ret a) >>= (λ x → lift (f ⁏ g) (d x)) by refl
            ≈ lift (f ⁏ g) (d a) by refl
            ≈ lift f (lift g (d a)) by lemma4-1 (d a)
                -- we can use 'lemma4-1' by the induction hypothesis 
            ≈ lift f (ret a >>= (λ x → lift g (d x))) by refl
          
        prop (invk u v) = 
          let
            open Eq {_} {w1 ⇒ _} _≐_ refl sym trans
          in
            ∵ (lift f (invk u v) >>= (λ x → lift (f ⁏ g) (d x))) 
              ≈ (f u >>= (λ y → lift f (v y))) >>= (λ z → lift (f ⁏ g) (d z)) by refl
                   -- <- L in the paper
              ≈  f u >>= (λ y → lift f (v y) >>= (λ z → lift (f ⁏ g) (d z)))
                   -- <- M in the paper
                by monad-assoc (λ y → lift f (v y)) (λ z → lift (f ⁏ g) (d z)) (f u)
              ≈ f u >>= (λ y → lift f (v y >>= (λ z → lift g (d z))))
                by bind-cong {p = f u} {q = f u} refl (λ a0 → prop (v a0))
                   -- <- R in the paper
                   -- NOTE: We must write "{p = f u} {q = f u}"
              ≈ lift f (invk u v >>= (λ x → lift g (d x))) by refl

-- Theorem 5: There exists a category W m of worlds and world maps.
-- (Proof: by the Lemma 3 and 4.)

----------------------------------------------------

-- Theorem 6: The product of a family of worlds is a categorical product
-- in the category of worlds and world maps.

