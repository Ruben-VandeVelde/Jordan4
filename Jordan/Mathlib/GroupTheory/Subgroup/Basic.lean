/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.group_theory__subgroup__basic
-/
import Mathlib.Data.Fintype.Perm

theorem Monoid.isCommutative_of_fintype_card_le_2
    {G : Type _} [DecidableEq G] [Fintype G] [Monoid G] (hG : Fintype.card G ≤ 2) :
    Std.Commutative (α := G) (· * ·) := by
  suffices ∀ (a b : G) (_ : a ≠ 1) (_ : b ≠ 1), a = b by
    constructor
    intro a b
    obtain rfl|ha := eq_or_ne a 1
    · simp only [one_mul, mul_one]
    obtain rfl|hb := eq_or_ne b 1
    · simp only [one_mul, mul_one]
    rw [this a b ha hb]
  contrapose! hG with h
  obtain ⟨a, b, ha1, hb1, hab⟩ := h
  rw [Fintype.two_lt_card_iff]
  exact ⟨a, b, 1, hab, ha1, hb1⟩

theorem Equiv.Perm.isCommutative_iff {α : Type _} [DecidableEq α] [Fintype α] :
    Std.Commutative (α := Equiv.Perm α) (· * ·) ↔ Fintype.card α ≤ 2 := by
  constructor
  · contrapose!
    intro hα h
    rw [Fintype.two_lt_card_iff] at hα
    obtain ⟨a, b, c, hab, hac, hbc⟩ := hα
    apply hbc
    -- follows from applying `(a c) (a b) = (a b) (a c)` to `a`
    convert Equiv.ext_iff.mp (h.comm (Equiv.swap a c) (Equiv.swap a b)) a
    rw [coe_mul, Function.comp_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hab.symm hbc]
    rw [coe_mul, Function.comp_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  · intro hα
    apply Monoid.isCommutative_of_fintype_card_le_2
    rw [← Nat.factorial_two, Fintype.card_perm]
    exact Nat.factorial_le hα
