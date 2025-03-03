/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module blocks
-/

import Jordan.Mathlib.Stabilizer
import Jordan.SubMulActions

import Mathlib.Data.Setoid.Partition
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Data.Setoid.Partition.Card

/-! # Blocks

Given `has_smul G X`, an action of a group `G` on a type `X`, we define

- the predicate `IsBlock G B` states that `B : set X` is a block,
which means that the sets `g • B`, for `g ∈ G` form a partition of `X`.

- a bunch of lemmas that gives example of “trivial” blocks : ⊥, ⊤, singletons, orbits…

-/

namespace MulAction

section Group

variable {G : Type _} [Group G] {X : Type _} [MulAction G X]

theorem IsBlock_image {H Y : Type _} [Group H] [MulAction H Y] {φ : G → H} (j : X →ₑ[φ] Y)
    (hφ : Function.Surjective φ) (hj : Function.Injective j) {B : Set X} (hB : IsBlock G B) :
    IsBlock H (j '' B) := by
  simp only [IsBlock, hφ.forall, ← image_smul_setₛₗ]
  exact fun g₁ g₂ hg ↦ Set.disjoint_image_of_injective hj <| hB <| ne_of_apply_ne _ hg

end Group

end MulAction
