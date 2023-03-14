/-
 Copyright 2023 RISC Zero, Inc.

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Mathlib.Algebra.Parity
-- A convenient way to import Nat and Order lemmas; linarith itself not used herein
import Mathlib.Tactic.Linarith

namespace R0sy.Lean.Nat

/- Serialize/deserialize helpers -/

def Nat.toUInt32Words (words: Nat) (val: Nat) (out: Array UInt32 := #[]): Array UInt32
  := match words with
      | 0 => out
      | words + 1 => Nat.toUInt32Words words (val >>> 32) (out.push (UInt32.ofNat val))

def Nat.fromUInt32Words (x: Subarray UInt32) (i: Nat := 0) (out: Nat := 0): Nat
  := if i < x.size
      then Nat.fromUInt32Words x (i + 1) ((out <<< 32) ||| UInt32.toNat x[x.size - i - 1]!)
      else out
termination_by _ => x.size - i

/- Log2 -/

@[simp]
theorem one_shl_eq_pow : 1 <<< n = 2 ^ n := by induction n <;> simp

private theorem Nat.log2_X_termination (h : 2 ^ y < x) : x - 2 ^ (y + 1) < x - 2 ^ y :=
  Nat.pow_succ _ _ ▸ Nat.sub_lt_sub_left (one_shl_eq_pow ▸ h) (by simp)

def Nat.log2_ceil (value: Nat) (result: Nat := 0): Nat :=
  if h : (1 <<< result) < value
  then log2_ceil value (result + 1)
  else result
termination_by _ => value - (2 ^ result)
decreasing_by exact Nat.log2_X_termination (one_shl_eq_pow ▸ h)

def Nat.log2_floor (value: Nat) (result: Nat := 0): Nat :=
  if h : (1 <<< (result + 1)) > value
  then result
  else log2_floor value (result + 1)
termination_by _ => value - (2 ^ result)
decreasing_by have : 1 <<< result < value := by
                rw [one_shl_eq_pow] at *
                rw [not_lt] at h
                by_cases eq : value ≤ 2 ^ result
                · have : 2 ^ (result + 1) ≤ 2 ^ result := le_trans h eq
                  simp [Nat.pow_succ] at this
                · rw [← not_le]; exact eq
              exact Nat.log2_X_termination (one_shl_eq_pow ▸ this)

end R0sy.Lean.Nat

namespace R0sy.Wheels

-- TODO(use newer mathlib4 with Nat.Parity)
-- Some code borrowed from: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Nat/Parity.lean
-- with the accompanying license:
/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Benjamin Davidson
! This file was ported from Lean 3 source module data.nat.parity
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
theorem mod_two_eq_zero_or_one (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  have := @Nat.mod_lt n 2 (by decide)
  revert this
  generalize eq : n % 2 = m
  intros h
  rcases m with _ | m <;> simp
  rcases m with _ | m <;> simp
  linarith

@[simp]
theorem mod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by
  cases' mod_two_eq_zero_or_one n with h h <;> simp [h]

theorem even_iff : Even n ↔ n % 2 = 0 :=
  ⟨
    λ ⟨m, h⟩ => by simp [← two_mul, h],
    λ h => ⟨n / 2, (Nat.div_add_mod n 2).symm.trans (by simp [← two_mul, h])⟩
  ⟩

instance : DecidablePred (Even : Nat → Prop) := λ _ => decidable_of_iff _ even_iff.symm

theorem odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨
    λ ⟨m, h⟩ => by rw [h, Nat.add_mod, Nat.mul_mod_right]; rfl,
    λ h => ⟨n / 2, (Nat.mod_add_div n 2).symm.trans (by rw [h, add_comm])⟩
  ⟩

instance : DecidablePred (Odd : Nat → Prop) := λ _ => decidable_of_iff _ odd_iff.symm

theorem not_even_iff : ¬Even n ↔ n % 2 = 1 := by rw [even_iff, mod_two_ne_zero]

@[simp]
theorem odd_iff_not_even {n : Nat} : Odd n ↔ ¬Even n := by rw [not_even_iff, odd_iff]

theorem even_or_odd (n : Nat) : Even n ∨ Odd n := by
  simp [odd_iff_not_even, Decidable.em (Even n)]

@[simp]
theorem bw_and_zero : Nat.bitwise and k 0 = 0 := by unfold Nat.bitwise; simp

theorem land_one_eq_0_iff_n_mod_2_eq_0 : n &&& 1 = 0 ↔ Even n := by
  simp only [even_iff, HAnd.hAnd, AndOp.and, Nat.land]
  unfold Nat.bitwise
  simp only [ite_false, decide_True, Bool.and_true, decide_eq_true_eq]
  rcases n with _ | k
  · rfl
  · simp only [Nat.succ_ne_zero, ite_false]
    have : 1 / 2 = 0 := by decide
    by_cases h₁ : Nat.succ k % 2 = 1 <;> simp [h₁, *]
    have := mod_two_eq_zero_or_one (k + 1)
    tauto

theorem div_two_of_odd {n : Nat} (h : Odd n) : (n - 1) / 2 = n / 2 := by
  rw [odd_iff] at h
  rw [← h, ← Nat.div_eq_sub_mod_div]

end R0sy.Wheels