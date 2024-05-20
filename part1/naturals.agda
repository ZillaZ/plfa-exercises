data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ


{- Seven exercise :D -}
seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc (zero)))))))

{- Eq exercise -}
{-# BUILTIN NATURAL ℕ #-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

{- Add -}
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
    ≡⟨⟩
      suc (2 + 4)
    ≡⟨⟩
      suc (suc (1 + 4))
    ≡⟨⟩
      suc (suc (suc (0 + 4)))
    ≡⟨⟩
      suc (suc (suc (4)))
    ≡⟨⟩
      7
   ∎

{- Mul -}
_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (4 * 0)))
  ≡⟨⟩
    12
  ∎

{- Exp -}
_^_ : ℕ → ℕ → ℕ
zero ^ n = zero
n ^ zero = suc zero
n ^ suc(m) = n * (n ^ m)

_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    81
 ∎

_∸_ : ℕ → ℕ → ℕ
n ∸ zero = n
zero ∸ suc n = zero
(suc m) ∸ (suc n) = m ∸ n

_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    2 ∸  0
  ≡⟨⟩
    2
  ∎

_ : 3 ∸ 5 ≡ zero
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    zero ∸ 2
  ≡⟨⟩
    zero
  ∎

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc(⟨⟩ O) ≡ ⟨⟩ I
_ = refl

_ : inc(⟨⟩ I) ≡ ⟨⟩ I O
_ = refl

_ : inc(⟨⟩ I O) ≡ ⟨⟩ I I
_ = refl

_ : inc(⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl

_ : inc(⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

{- Conversions -}
from : Bin → ℕ

from ⟨⟩ = zero
from (⟨⟩ O) = zero
from (⟨⟩ I) = suc (zero)
from (b O) = from (b) * 2
from (b I) = (from (b) * 2) + suc (zero)

_ : from (⟨⟩ O) ≡ zero
_ = refl
_ : from (⟨⟩ I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to (n))

_ : to (0) ≡ ⟨⟩ O
_ = refl

_ : to (1) ≡ ⟨⟩ I
_ = refl

_ : to (2) ≡ ⟨⟩ I O
_ = refl

_ : to (3) ≡ ⟨⟩ I I
_ = refl

_ : to (4) ≡ ⟨⟩ I O O
_ = refl
