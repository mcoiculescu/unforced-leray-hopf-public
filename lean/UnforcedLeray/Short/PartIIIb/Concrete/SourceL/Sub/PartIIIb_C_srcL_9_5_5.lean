import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5

/-!
# Decomposition of `SCSDeriv` (source 4178-4186, 4917-4937)

Source: `the November 2 reference manuscript`.
`SCSDeriv` follows from: the line-restriction bound `SDLine`, the one-variable Euler-operator bound
`SDEuler` (`(s∂_s) = -½ r∂_r`), and the matrix-to-entries bookkeeping `SDMat`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `s ∂_s` on real functions (local copy; `AffineEnvelope.sDerivR` cannot be imported here). -/
def sDerivS (f : ℝ → ℝ) : ℝ → ℝ := fun s => s * deriv f s

/-- `(s ∂_s)^i` on real functions. -/
def sDerivIterS : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | i + 1, f => sDerivS (sDerivIterS i f)

/-- Line restriction (source 4917-4937): for `X` that is `C^7` off the axis with
`‖D^m X(y)‖ ≤ K r^{-4-m}`, the entries `h_{i,j}(r) = D X(r,0,0)[e_j]_i` are `C^6` on `(0,∞)` and
`|h^{(k)}(r)| ≤ K r^{-5-k}` for `k ≤ 6` (`h^{(k)}(r) = D^{k+1}X(r e₁)[e₁,…,e₁,e_j]_i`,
`‖·‖ ≤ ‖D^{k+1}X‖`, `cylR (r,0,0) = r`; use `norm_iteratedFDeriv_comp_right`-type lemmas along
`t ↦ ![t,0,0]` and `ContinuousMultilinearMap.norm_apply_le`/`le_opNorm`). -/
def SDLine : Prop :=
  ∀ (X : Vec3 → Vec3) (K : ℝ), 0 ≤ K → (∀ y : Vec3, 0 < cylR y → ContDiffAt ℝ 7 X y) →
    (∀ m : ℕ, m ≤ 7 → ∀ y : Vec3, 0 < cylR y →
      ‖iteratedFDeriv ℝ m X y‖ ≤ K * cylR y ^ (-(4 : ℝ) - m)) →
    ∀ i j : Fin 3,
      ContDiffOn ℝ 6 (fun r : ℝ => fderiv ℝ X ![r, 0, 0] (Pi.single j 1) i) (Ioi 0) ∧
      ∀ k : ℕ, k ≤ 6 → ∀ r : ℝ, 0 < r →
        |iteratedDeriv k (fun r : ℝ => fderiv ℝ X ![r, 0, 0] (Pi.single j 1) i) r| ≤
          K * r ^ (-(5 : ℝ) - k)

/-- Euler operator (source 4917-4937): for `h` `C^6` on `(0,∞)` with
`|h^{(k)}(r)| ≤ M r^{-5-k}` (`k ≤ 6`) and `g(s) = h(s^{-1/2})` (zero for `s ≤ 0`),
`|(s∂_s)^j g(s)| ≤ C M s^{5/2}` for `j ≤ 6`, `C` absolute.  With `r = s^{-1/2}`,
`s∂_s = -½ r∂_r` and `(r∂_r)^j h = Σ_{k=1}^{j} a_{j,k} r^k h^{(k)}` (or `k=0..j`) with integer
`a_{j,k}` (induction: `r∂_r(r^k h^{(k)}) = k r^k h^{(k)} + r^{k+1} h^{(k+1)}`); each term is
`≤ M r^{-5} = M s^{5/2}`. -/
def SDEuler : Prop :=
  ∃ C : ℝ, ∀ (h : ℝ → ℝ) (M : ℝ), 0 ≤ M → ContDiffOn ℝ 6 h (Ioi 0) →
    (∀ k : ℕ, k ≤ 6 → ∀ r : ℝ, 0 < r → |iteratedDeriv k h r| ≤ M * r ^ (-(5 : ℝ) - k)) →
    ∀ s : ℝ, 0 < s → ∀ j : ℕ, j ≤ 6 →
      |sDerivIterS j (fun s : ℝ => if 0 < s then h ((1 : ℝ)⁻¹ / Real.sqrt s) else 0) s| ≤
        C * M * s ^ (5 / 2 : ℝ)

/-- Matrix bookkeeping: if every entry of `A : ℝ → Mat3` is `C^6` on `(0,∞)`, then for `s > 0`,
`j ≤ 6`, `(s∂_s)^j` acts entrywise (`deriv` of a `Fin 3 → Fin 3 → ℝ`-valued map is entrywise,
locally near `s`) and `frob B ≤ Σ_{i,i'} |B i i'|`. -/
def SDMat : Prop :=
  ∀ A : ℝ → Mat3, (∀ i i' : Fin 3, ContDiffOn ℝ 6 (fun s => A s i i') (Ioi 0)) →
    ∀ s : ℝ, 0 < s → ∀ j : ℕ, j ≤ 6 →
      frob (sDerivIter j A s) ≤ ∑ i : Fin 3, ∑ i' : Fin 3, |sDerivIterS j (fun s => A s i i') s|

theorem scSDeriv_of (hL : SDLine) (hE : SDEuler) (hM : SDMat) : SCSDeriv := by
  obtain ⟨C, hC⟩ := hE
  refine ⟨9 * |C|, ?_⟩
  intro X K hK hX hb s hs j hj
  set A : ℝ → Mat3 := fun s : ℝ => if 0 < s then
        (fun (i j : Fin 3) => fderiv ℝ X ![(1 : ℝ)⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1) i)
        else (0 : Mat3) with hA
  have key : ∀ i i' : Fin 3, (fun s : ℝ => A s i i') =
      (fun s : ℝ => if 0 < s then
        (fun r : ℝ => fderiv ℝ X ![r, 0, 0] (Pi.single i' 1) i) ((1 : ℝ)⁻¹ / Real.sqrt s)
        else 0) := by
    intro i i'
    funext s
    by_cases h : 0 < s <;> simp [hA, h]
  have hs1 : ∀ i i' : Fin 3, ContDiffOn ℝ 6 (fun s => A s i i') (Ioi 0) := by
    intro i i'
    rw [key]
    obtain ⟨h1, _⟩ := hL X K hK hX hb i i'
    have hg : ContDiffOn ℝ 6 (fun s : ℝ => (1 : ℝ)⁻¹ / Real.sqrt s) (Ioi 0) := by
      intro x hx
      have hx' : x ≠ 0 := ne_of_gt hx
      have : ContDiffAt ℝ 6 (fun s : ℝ => (1 : ℝ)⁻¹ / Real.sqrt s) x :=
        contDiffAt_const.div (Real.contDiffAt_sqrt hx') (Real.sqrt_ne_zero'.2 hx)
      exact this.contDiffWithinAt
    have hmap : MapsTo (fun s : ℝ => (1 : ℝ)⁻¹ / Real.sqrt s) (Ioi 0) (Ioi 0) := by
      intro x hx
      have : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
      simpa using this
    refine (h1.comp hg hmap).congr ?_
    intro x hx
    have : 0 < x := hx
    simp [this]
  have hs2 : ∀ i i' : Fin 3, |sDerivIterS j (fun s : ℝ => A s i i') s| ≤
      |C| * K * s ^ (5 / 2 : ℝ) := by
    intro i i'
    rw [key]
    obtain ⟨h1, h2⟩ := hL X K hK hX hb i i'
    exact (hC _ K hK h1 h2 s hs j hj).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hK)
        (Real.rpow_nonneg hs.le _))
  refine (hM A hs1 s hs j hj).trans ?_
  calc _ ≤ ∑ _i : Fin 3, ∑ _i' : Fin 3, |C| * K * s ^ (5 / 2 : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => hs2 i i'
    _ = 9 * |C| * K * s ^ (5 / 2 : ℝ) := by simp; ring

end UnforcedLeray.Short.PartIIIb.Concrete
