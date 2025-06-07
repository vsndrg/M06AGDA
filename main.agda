data N : Set where
  zero : N
  suc : N → N

{-# BUILTIN NATURAL N #-}

infixl 6 _+_
_+_ : N → N → N
_+_ 0 x = x
_+_ (suc y) x = suc (y + x)

infixl 7 _*_
_*_ : N → N → N
_*_ 0 x = 0
_*_ (suc y) x = x + y * x

-- open import Agda.Builtin.Equality

open import Relation.Binary.PropositionalEquality as A
open A.≡-Reasoning

plus-zero : (x : N) → x + 0 ≡ x
plus-zero 0 = refl
plus-zero (suc x) = 
  begin
    suc x + 0 ≡⟨⟩ suc (x + 0)
    ≡⟨ cong suc (plus-zero x) ⟩ suc x
  ∎

add-assoc : (a b c : N) → a + (b + c) ≡ a + b + c
add-assoc 0 b c = refl
add-assoc (suc a) b c =
  begin
    suc a + (b + c) ≡⟨⟩ suc (a + (b + c)) ≡⟨ cong suc (add-assoc a b c) ⟩ suc (a + b + c)
  ∎

plus-suc : (a b : N) → a + suc b ≡ suc (a + b)
plus-suc 0 b = refl
plus-suc (suc a) b =
  begin
    suc a + suc b ≡⟨⟩ suc (a + suc b) ≡⟨ cong suc (plus-suc a b) ⟩ suc (suc (a + b)) ≡⟨⟩ suc (suc a + b)
  ∎

add-comm : (a b : N) → a + b ≡ b + a
add-comm 0 b = sym (plus-zero b)
add-comm (suc a) b =
  begin
    suc a + b ≡⟨⟩ suc (a + b) ≡⟨ cong suc (add-comm a b) ⟩ suc (b + a) ≡⟨ sym (plus-suc b a) ⟩ b + suc a
  ∎

mul-zero : (a : N) → a * 0 ≡ 0
mul-zero 0 = refl
mul-zero (suc a) = mul-zero a

{-
mul-comm : (a b : N) → a * b ≡ b * a
mul-comm 0 b = sym (mul-zero b)
mul-comm (suc a) b =
  begin
    suc a * b ≡⟨⟩ b + a * b ≡⟨ ? ⟩ b * suc a
  ∎

mul-assoc : (a b c : N) → a * b * c ≡ a * (b * c)
mul-assoc 0 b c = refl
mul-assoc (suc a) b c =
  begin
    suc a * b * c ≡⟨⟩ (b + a * b) * c ≡⟨ ? ⟩ suc a * (b * c)
  ∎
-}

