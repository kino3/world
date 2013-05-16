{-# OPTIONS --universe-polymorphism #-}

----------------------------------------------------
-- Equality library
-- created  by Yoshiki KINOSHITA
-- modified by Shuji KINOSHITA
----------------------------------------------------

open import Level
module Eq {ℓ} {A : Set ℓ} (_∼_ : A → A → Set ℓ)
  (refl : {a : A} → a ∼ a)
  (sym : {a b : A} → b ∼ a → a ∼ b)
  (trans : {a b c : A} → a ∼ b → b ∼ c → a ∼ c) where
  infixl 1 _≈_by_
  infixl 1 _≈_yb_
  ∵ : (a : A) → a ∼ a
  ∵ a = refl 
  _≈_by_ : {x y : A} → x ∼ y → (z : A) → y ∼ z → x ∼ z
  e ≈ _ by r = trans e r
  _≈_yb_ : {x y : A} → x ∼ y → (z : A) → z ∼ y → x ∼ z
  e ≈ _ yb r = trans e (sym r)

{-
以下は、別のファイルで、上記を呼び出す例。
_≡_ に限らず、同値関係なら何でも実パラメータに
して使える。

-- Using Example

open import Relation.Binary.Core
  using (_≡_; refl)
open import Data.Nat
sym : {a b : ℕ} → b ≡ a → a ≡ b
sym {a} {.a} refl = refl
trans :  {a b c : ℕ} → b ≡ c → a ≡ b → a ≡ c
trans {a} {.a} {.a} refl refl = refl
open Eq {_} {ℕ} _≡_ refl sym trans

p : 3 ≡ 3
p = ∵ 3 ≈ 3 by refl
          ≈ 3 by refl
-}