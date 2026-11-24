import UnforcedLeray.Short.PartI.Sub.T02_1_4_4_1

/-!
# Part I, `PartI:T02/1/4/4/1/2`: the advection step `m → m + 1`, reduced to five lemmas

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic: the mild solution is smooth; the `H^m` product estimate `H^{m+1} × H^{m+1} →
H^m` for the advection term `∑ v_i ∂_i w`, propagated from level `m` to level `m + 1`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB


local notation "𝓗[" c "," k "]" => Cyl.H ℝ Cyl.Vec2 c 0 k

theorem wμ_zero_eq (c : ℝ) :
    Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = Cyl.cellμ c := by
  rw [Cyl.wμ_ρwW, Cyl.wμ]
  have h1 : (fun z => ENNReal.ofReal (Cyl.ρw c z ^ (0 : ℝ))) = 1 := by
    funext z; simp
  rw [h1, MeasureTheory.withDensity_one]

theorem ae_wμ_le (c : ℝ) :
    MeasureTheory.ae (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) ≤
      MeasureTheory.ae (Cyl.cellμ c) := by
  rw [wμ_zero_eq]

theorem ae_cell_le (c : ℝ) :
    MeasureTheory.ae (Cyl.cellμ c) ≤
      MeasureTheory.ae (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
  rw [wμ_zero_eq]

theorem ae_cyl_le (c : ℝ) :
    MeasureTheory.ae (Sob.cylinder c).μ ≤ MeasureTheory.ae (Cyl.cellμ c) := by
  rw [Cyl.cylinder_μ_eq]

theorem hVal_ext {c : ℝ} {m : ℕ} {x y : 𝓗[c, m]}
    (h : hVal x =ᵐ[Cyl.cellμ c] hVal y) : x = y := by
  apply Sob.W.value_injective
  apply MeasureTheory.Lp.ext
  exact h.filter_mono (ae_wμ_le c)

theorem hVal_add {c : ℝ} {m : ℕ} (a b : 𝓗[c, m]) :
    hVal (a + b) =ᵐ[Cyl.cellμ c] hVal a + hVal b := by
  unfold hVal
  rw [map_add]
  exact (Lp.coeFn_add _ _).filter_mono (ae_cell_le c)

theorem hVal_smul {c : ℝ} {m : ℕ} (r : ℝ) (a : 𝓗[c, m]) :
    hVal (r • a) =ᵐ[Cyl.cellμ c] r • hVal a := by
  unfold hVal
  rw [map_smul]
  exact (Lp.coeFn_smul _ _).filter_mono (ae_cell_le c)

/-- **Lemma N1 (analytic core).**  The weak product rule for a scalar times a vector, both factors
in the first Sobolev level on the cylinder: if `a, u` are square integrable on the cell with square
integrable weak `∂_j`-derivatives `a', u'`, then `a • u` has weak `∂_j`-derivative
`a' • u + a • u'` (source lines 261-288).  Proof idea: approximate `a, u` in `H^1` of the cell by
smooth cylinder fields (`W.cylinder_dense_smooth`), apply the classical Leibniz rule to the
approximants, and pass to the limit in `L^1` on each bounded `η`-strip using Cauchy-Schwarz
(in dimension `2`, `H^1 · H^1 ⊂ W^{1,1}`).  The whole-space analogue is `Sob.HasWeakDeriv.bilin`
(`Lib/SobolevB/Bilin.lean`). -/
def CylWeakProductSmul : Prop :=
  ∀ (c : ℝ) (j : Fin 2) (a a' : Plane → ℝ) (u u' : Plane → Cyl.Vec2),
    MemLp a 2 (Cyl.cellμ c) → MemLp a' 2 (Cyl.cellμ c) →
    MemLp u 2 (Cyl.cellμ c) → MemLp u' 2 (Cyl.cellμ c) →
    Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir j] a a' →
    Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir j] u u' →
    Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir j]
      (fun z => a z • u z) (fun z => a' z • u z + a z • u' z)

/-- **Lemma N2 (gluing of the first derivatives).**  Given `x ∈ H^m` and `y_j ∈ H^m` such that
`y_j` is the weak `∂_j`-derivative of `x` for each `j`, there is `X ∈ H^{m+1}` with the value of
`x` and first partial derivatives `y_j` (source lines 261-288).  Proof idea: define the components
of `X` by the first letter of each word (`deriv (cons j β) X := deriv β (y j)`, and the empty word
is the value of `x`); each word `cylDir j :: word β` is a weak derivative by
`HasWeakDeriv.append`; use `Sob.W.ofFields`. -/
def CylGlueFirstOrder : Prop :=
  ∀ (c : ℝ) (m : ℕ) (x : 𝓗[c, m]) (y : Fin 2 → 𝓗[c, m]),
    (∀ j : Fin 2, Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir j] (hVal x) (hVal (y j))) →
    ∃ X : 𝓗[c, m + 1],
      hVal X =ᵐ[Cyl.cellμ c] hVal x ∧
      ∀ j : Fin 2, hVal (Sob.W.partialDeriv (k := m) j X) =ᵐ[Cyl.cellμ c] hVal (y j)

/-- **Lemma N3 (commutation of mixed weak derivatives).**  For `x ∈ H^{k+2}` the two mixed
second-order components agree a.e. (source lines 261-288).  Proof idea: `HasWeakDeriv.perm`
(the words `[i, j]` and `[j, i]` are permutations) with `HasWeakDeriv.ae_unique`. -/
def CylWeakDerivCommute : Prop :=
  ∀ (c : ℝ) (k : ℕ) (i j : Fin 2) (x : 𝓗[c, k + 2]),
    hVal (Sob.W.partialDeriv (k := k) i (Sob.W.partialDeriv (k := k + 1) j x)) =ᵐ[Cyl.cellμ c]
      hVal (Sob.W.partialDeriv (k := k) j (Sob.W.partialDeriv (k := k + 1) i x))

/-- **Lemma N4 (norm bound one level up).**  `‖x‖ ≤ ‖res x‖ + ∑_j ‖∂_j x‖` for `x ∈ H^{m+1}`
(source lines 261-288).  Proof idea: `Sob.W.norm_sq` and the decomposition of the words of length
`≤ m + 1` as the empty word and `cons j β`, giving `‖x‖² = ‖res x‖² + ∑_j ‖∂_j x‖²`-type
identity, then `Real.sqrt_le_sqrt` and `sqrt (a + b) ≤ sqrt a + sqrt b`. -/
def CylSobNormSucc : Prop :=
  ∀ (c : ℝ) (m : ℕ) (x : 𝓗[c, m + 1]),
    ‖x‖ ≤ ‖(Sob.W.restrict (Nat.le_succ m) x : 𝓗[c, m])‖ +
      ∑ j : Fin 2, ‖(Sob.W.partialDeriv (k := m) j x : 𝓗[c, m])‖

/-- **Lemma N5 (weak Leibniz rule for the advection term, from N1 and N3).**  For `v, w ∈ H^{m+2}`
and each `j`, the field `f = ∑_i v_i ∂_i w` (with `v, w` restricted to `H^{m+1}`) has weak
`∂_j`-derivative `∑_i (∂_j v)_i ∂_i w + v_i ∂_i ∂_j w` (source lines 261-288).  Proof idea:
`HasWeakDeriv.sum` over `i`, `CylWeakProductSmul` for each `v_i • ∂_i w` (components via
`HasWeakDeriv.map_clm`, the weak derivatives of `v`, `∂_i w` from `Sob.W.hasWeakDeriv` and
`value_partialDeriv`), `CylWeakDerivCommute` to turn `∂_j ∂_i w` into `∂_i ∂_j w`. -/
def AdvectionWeakLeibniz : Prop :=
  ∀ (c : ℝ) (m : ℕ) (v w : 𝓗[c, m + 2]) (j : Fin 2),
    Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir j]
      (fun z => ∑ i : Fin 2,
        (hVal (Sob.W.restrict (by omega : m + 1 ≤ m + 2) v : 𝓗[c, m + 1]) z i) •
          hVal (Sob.W.partialDeriv (k := m)
            i (Sob.W.restrict (by omega : m + 1 ≤ m + 2) w : 𝓗[c, m + 1])) z)
      (fun z => ∑ i : Fin 2,
        ((hVal (Sob.W.partialDeriv (k := m + 1) j v) z i) •
            hVal (Sob.W.partialDeriv (k := m)
              i (Sob.W.restrict (by omega : m + 1 ≤ m + 2) w : 𝓗[c, m + 1])) z +
          (hVal (Sob.W.restrict (by omega : m + 1 ≤ m + 2) v : 𝓗[c, m + 1]) z i) •
            hVal (Sob.W.partialDeriv (k := m) i (Sob.W.partialDeriv (k := m + 1) j w)) z))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 8000000 in
/-- The advection step from the lemmas N2, N4, N5 (N1 and N3 enter through N5). -/
theorem advectionStep_of (h1 : CylGlueFirstOrder) (h2 : CylSobNormSucc)
    (h4 : AdvectionWeakLeibniz) : AdvectionStep := by
  intro c hc hc1 m hm hAdv
  obtain ⟨B, hB⟩ := hAdv
  let r : 𝓗[c, m + 2] →L[ℝ] 𝓗[c, m + 1] := Sob.W.restrict (by omega : m + 1 ≤ m + 2)
  let d : Fin 2 → 𝓗[c, m + 2] →L[ℝ] 𝓗[c, m + 1] := fun j => Sob.W.partialDeriv (k := m + 1) j
  let xf : 𝓗[c, m + 2] → 𝓗[c, m + 2] → 𝓗[c, m] := fun v w => B (r v) (r w)
  let yf : Fin 2 → 𝓗[c, m + 2] → 𝓗[c, m + 2] → 𝓗[c, m] :=
    fun j v w => B (d j v) (r w) + B (r v) (d j w)
  have ex : ∀ v w : 𝓗[c, m + 2], ∃ X : 𝓗[c, m + 1],
      hVal X =ᵐ[Cyl.cellμ c] hVal (xf v w) ∧
      ∀ j : Fin 2, hVal (Sob.W.partialDeriv (k := m) j X) =ᵐ[Cyl.cellμ c] hVal (yf j v w) := by
    intro v w
    refine h1 c m (xf v w) (fun j => yf j v w) (fun j => ?_)
    have hl := h4 c m v w j
    refine hl.congr_ae ?_ ?_
    · exact ((hB (r v) (r w)).symm).filter_mono (ae_cyl_le c)
    · refine Filter.EventuallyEq.filter_mono ?_ (ae_cyl_le c)
      have e1 := hB (d j v) (r w)
      have e2 := hB (r v) (d j w)
      filter_upwards [hVal_add (B (d j v) (r w)) (B (r v) (d j w)), e1, e2] with z h h1' h2'
      show _ = hVal (B (d j v) (r w) + B (r v) (d j w)) z
      rw [h]
      simp only [Pi.add_apply]
      rw [h1', h2', ← Finset.sum_add_distrib]
  choose X hX using ex
  have hXext : ∀ v w (X' : 𝓗[c, m + 1]), hVal X' =ᵐ[Cyl.cellμ c] hVal (xf v w) → X' = X v w :=
    fun v w X' h => hVal_ext (h.trans (hX v w).1.symm)
  obtain ⟨K, hK0, hKb⟩ := (ContinuousLinearMap.isBoundedBilinearMap (𝕜 := ℝ) B).bound
  have hBb : ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖ := fun x y => hKb x y
  let R : ℝ := ‖r‖
  let D : Fin 2 → ℝ := fun j => ‖d j‖
  let C : ℝ := K * R ^ 2 + ∑ j : Fin 2, 2 * K * D j * R
  let L : 𝓗[c, m + 2] →ₗ[ℝ] 𝓗[c, m + 2] →ₗ[ℝ] 𝓗[c, m + 1] :=
    LinearMap.mk₂ ℝ X
      (fun v₁ v₂ w => by
        refine (hXext (v₁ + v₂) w (X v₁ w + X v₂ w) ?_).symm
        have e : xf (v₁ + v₂) w = xf v₁ w + xf v₂ w := by simp [xf, map_add]
        rw [e]
        filter_upwards [hVal_add (X v₁ w) (X v₂ w), hVal_add (xf v₁ w) (xf v₂ w),
          (hX v₁ w).1, (hX v₂ w).1] with z h1' h2' h3' h4'
        rw [h1', h2']
        simp [h3', h4'])
      (fun a v w => by
        refine (hXext (a • v) w (a • X v w) ?_).symm
        have e : xf (a • v) w = a • xf v w := by simp [xf, map_smul]
        rw [e]
        filter_upwards [hVal_smul a (X v w), hVal_smul a (xf v w), (hX v w).1] with z h1' h2' h3'
        rw [h1', h2']
        simp [h3'])
      (fun v w₁ w₂ => by
        refine (hXext v (w₁ + w₂) (X v w₁ + X v w₂) ?_).symm
        have e : xf v (w₁ + w₂) = xf v w₁ + xf v w₂ := by simp [xf, map_add]
        rw [e]
        filter_upwards [hVal_add (X v w₁) (X v w₂), hVal_add (xf v w₁) (xf v w₂),
          (hX v w₁).1, (hX v w₂).1] with z h1' h2' h3' h4'
        rw [h1', h2']
        simp [h3', h4'])
      (fun a v w => by
        refine (hXext v (a • w) (a • X v w) ?_).symm
        have e : xf v (a • w) = a • xf v w := by simp [xf, map_smul]
        rw [e]
        filter_upwards [hVal_smul a (X v w), hVal_smul a (xf v w), (hX v w).1] with z h1' h2' h3'
        rw [h1', h2']
        simp [h3'])
  have hbound : ∀ v w : 𝓗[c, m + 2], ‖L v w‖ ≤ C * ‖v‖ * ‖w‖ := by
    intro v w
    have hL : L v w = X v w := rfl
    rw [hL]
    have hres : (Sob.W.restrict (Nat.le_succ m) (X v w) : 𝓗[c, m]) = xf v w :=
      hVal_ext (hX v w).1
    have hpart : ∀ j, (Sob.W.partialDeriv (k := m) j (X v w) : 𝓗[c, m]) = yf j v w :=
      fun j => hVal_ext ((hX v w).2 j)
    have h2' := h2 c m (X v w)
    rw [hres] at h2'
    simp only [hpart] at h2'
    have hR0 : 0 ≤ R := norm_nonneg r
    have hrv : ‖r v‖ ≤ R * ‖v‖ := r.le_opNorm v
    have hrw : ‖r w‖ ≤ R * ‖w‖ := r.le_opNorm w
    have hdv : ∀ j, ‖d j v‖ ≤ D j * ‖v‖ := fun j => (d j).le_opNorm v
    have hdw : ∀ j, ‖d j w‖ ≤ D j * ‖w‖ := fun j => (d j).le_opNorm w
    have hx : ‖xf v w‖ ≤ K * R ^ 2 * (‖v‖ * ‖w‖) := by
      calc ‖xf v w‖ ≤ K * ‖r v‖ * ‖r w‖ := hBb _ _
        _ ≤ K * (R * ‖v‖) * (R * ‖w‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hrv hK0.le) hrw (norm_nonneg _)
            (mul_nonneg hK0.le (mul_nonneg hR0 (norm_nonneg _)))
        _ = K * R ^ 2 * (‖v‖ * ‖w‖) := by ring
    have hy : ∀ j, ‖yf j v w‖ ≤ 2 * K * D j * R * (‖v‖ * ‖w‖) := by
      intro j
      calc ‖yf j v w‖ ≤ ‖B (d j v) (r w)‖ + ‖B (r v) (d j w)‖ := norm_add_le _ _
        _ ≤ K * ‖d j v‖ * ‖r w‖ + K * ‖r v‖ * ‖d j w‖ :=
          add_le_add (hBb _ _) (hBb _ _)
        _ ≤ K * (D j * ‖v‖) * (R * ‖w‖) + K * (R * ‖v‖) * (D j * ‖w‖) :=
          add_le_add
            (mul_le_mul (mul_le_mul_of_nonneg_left (hdv j) hK0.le) hrw (norm_nonneg _)
              (mul_nonneg hK0.le (mul_nonneg (norm_nonneg (d j)) (norm_nonneg _))))
            (mul_le_mul (mul_le_mul_of_nonneg_left hrv hK0.le) (hdw j) (norm_nonneg _)
              (mul_nonneg hK0.le (mul_nonneg hR0 (norm_nonneg _))))
        _ = 2 * K * D j * R * (‖v‖ * ‖w‖) := by ring
    calc ‖X v w‖ ≤ ‖xf v w‖ + ∑ j : Fin 2, ‖yf j v w‖ := h2'
      _ ≤ K * R ^ 2 * (‖v‖ * ‖w‖) + ∑ j : Fin 2, 2 * K * D j * R * (‖v‖ * ‖w‖) :=
          add_le_add hx (Finset.sum_le_sum fun j _ => hy j)
      _ = C * ‖v‖ * ‖w‖ := by
          rw [← Finset.sum_mul]
          simp only [C]
          ring
  refine ⟨LinearMap.mkContinuous₂ L C hbound, fun v w => ?_⟩
  have hL : LinearMap.mkContinuous₂ L C hbound v w = X v w := rfl
  rw [hL]
  filter_upwards [(hX v w).1, hB (r v) (r w)] with z h1' h2'
  rw [h1', h2']
  rfl

end UnforcedLeray.Short.PartI
