import UnforcedLeray.Short.PartIIb.Sub.T11_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.NiceClosure
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Cpd
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.HeatEq
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Smooth

/-!
# Part II-b, leaf `PartII-b:T11/3/8` (`HeatDerivDomination`): pointwise domination of the
derivatives of a heat flow by heat flows of nice streams

Source of record: `the November 2 reference manuscript`, SP 1923-1927.
The statement is `HeatDerivDomination` of `Sub/T11_3.lean`.

Proof. Induction on `n`, for all nice streams simultaneously, with the bound stored as a finite
list of nice streams (`hddList`). For `n + 1`:
* `‖D^{n+1} H x‖ = ‖D^n (fderiv H) x‖`, and `fderiv H y = Σ_j (cpd j H y) • π_j` with
  `‖π_j‖ ≤ 1` (coordinate functionals), so `‖D^n (fderiv H) x‖ ≤ Σ_j ‖D^n (cpd j H) x‖`.
* `cpd 1 H_ζ = H_{∂_q ζ}` and `cpd 2 H_ζ = H_{∂_η ζ}` near `x` (`HeatConvCpd`).
* `cpd 0 H_ζ = ν (H_{∂_q² ζ} + H_{∂_η² ζ})` near `x` (`HeatConvEq`, `HeatConvCpd`).
Apply the induction hypothesis to the nice streams `∂_q ζ`, `∂_η ζ`, `∂_q² ζ`, `∂_η² ζ`
(`NiceStreamClosure`) and concatenate the finite families.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- The three coordinate functionals of `Coord = ℝ × (ℝ × ℝ)` (`s`, `q`, `η`). -/
def hdd_proj : Fin 3 → (Coord →L[ℝ] ℝ) :=
  ![ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ),
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)),
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))]

lemma hdd_proj0_norm : ‖hdd_proj 0‖ ≤ 1 := by
  show ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1
  exact ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ)

lemma hdd_proj1_norm : ‖hdd_proj 1‖ ≤ 1 := by
  show ‖(ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))‖ ≤ 1
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
  have h2 := ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)
  calc ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ * ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖ ≤ 1 * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma hdd_proj2_norm : ‖hdd_proj 2‖ ≤ 1 := by
  show ‖(ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))‖ ≤ 1
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
  have h2 := ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)
  calc ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ * ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖ ≤ 1 * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Coordinate decomposition of a derivative on `Coord`. -/
lemma hdd_decomp (f : Coord → ℝ) (y v : Coord) :
    fderiv ℝ f y v = ∑ j : Fin 3, fderiv ℝ f y (cdir j) * hdd_proj j v := by
  have hv : v = v.1 • cdir 0 + v.2.1 • cdir 1 + v.2.2 • cdir 2 := by
    ext <;> simp [cdir]
  conv_lhs => rw [hv]
  rw [Fin.sum_univ_three]
  simp only [map_add, map_smul, smul_eq_mul]
  show _ = fderiv ℝ f y (cdir 0) * v.1 + fderiv ℝ f y (cdir 1) * v.2.1
    + fderiv ℝ f y (cdir 2) * v.2.2
  ring

/-- The derivative of `f` as a combination of the coordinate functionals. -/
lemma hdd_fderiv_eq (f : Coord → ℝ) (y : Coord) :
    fderiv ℝ f y = ∑ j : Fin 3, cpd j f y • hdd_proj j := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact hdd_decomp f y v

lemma hdd_fderiv_fun (f : Coord → ℝ) :
    fderiv ℝ f = fun y => ∑ j : Fin 3, cpd j f y • hdd_proj j :=
  funext (hdd_fderiv_eq f)

lemma hdd_norm_smulRight {n : ℕ} (P : Coord →L[ℝ] ℝ) (hP : ‖P‖ ≤ 1)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord) ℝ) :
    ‖((ContinuousLinearMap.id ℝ ℝ).smulRight P).compContinuousMultilinearMap T‖ ≤ ‖T‖ := by
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  have hS : ‖(ContinuousLinearMap.id ℝ ℝ).smulRight P‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    simp [hP]
  exact mul_le_of_le_one_left (norm_nonneg _) hS

lemma hdd_iter_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {F G : Coord → V}
    {n : ℕ} {x : Coord} (hF : ContDiffAt ℝ n F x) (hG : ContDiffAt ℝ n G x) :
    iteratedFDeriv ℝ n (fun y => F y + G y) x = iteratedFDeriv ℝ n F x + iteratedFDeriv ℝ n G x :=
  iteratedFDeriv_add_apply hF hG

lemma hdd_ca (n : ℕ) {f : Coord → ℝ} {x : Coord} (h : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ n f x :=
  h.of_le (by exact_mod_cast le_top)

/-- Splitting of the derivative of order `n` of `fderiv f` into the partial derivatives. -/
lemma hdd_split {f : Coord → ℝ} {x : Coord}
    (hD : ContDiffAt ℝ ∞ (fun y => fderiv ℝ f y) x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ ≤ ∑ j : Fin 3, ‖iteratedFDeriv ℝ n (cpd j f) x‖ := by
  have hc : ∀ j : Fin 3, ContDiffAt ℝ ∞ (cpd j f) x := fun j =>
    hD.clm_apply (contDiffAt_const (c := cdir j))
  have hcn : ∀ j : Fin 3, ContDiffAt ℝ n (cpd j f) x := fun j => hdd_ca n (hc j)
  rw [hdd_fderiv_fun f]
  simp only [Fin.sum_univ_three]
  have e0 : ContDiffAt ℝ n (fun y => cpd 0 f y • hdd_proj 0) x := (hcn 0).smul_const _
  have e1 : ContDiffAt ℝ n (fun y => cpd 1 f y • hdd_proj 1) x := (hcn 1).smul_const _
  have e2 : ContDiffAt ℝ n (fun y => cpd 2 f y • hdd_proj 2) x := (hcn 2).smul_const _
  rw [hdd_iter_add (e0.add e1) e2, hdd_iter_add e0 e1,
    iteratedFDeriv_smul_const_apply (hcn 0), iteratedFDeriv_smul_const_apply (hcn 1),
    iteratedFDeriv_smul_const_apply (hcn 2)]
  have h0 := hdd_norm_smulRight (hdd_proj 0) hdd_proj0_norm (iteratedFDeriv ℝ n (cpd 0 f) x)
  have h1 := hdd_norm_smulRight (hdd_proj 1) hdd_proj1_norm (iteratedFDeriv ℝ n (cpd 1 f) x)
  have h2 := hdd_norm_smulRight (hdd_proj 2) hdd_proj2_norm (iteratedFDeriv ℝ n (cpd 2 f) x)
  have t1 := norm_add_le
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (hdd_proj 0)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (cpd 0 f) x))
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (hdd_proj 1)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (cpd 1 f) x))
  have t2 := norm_add_le
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (hdd_proj 0)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (cpd 0 f) x) +
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (hdd_proj 1)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (cpd 1 f) x))
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (hdd_proj 2)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (cpd 2 f) x))
  linarith

lemma hdd_nhds {x : Coord} (hx : 0 < x.1) :
    (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ∈ 𝓝 x :=
  (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩

lemma hdd_ev {x : Coord} (hx : 0 < x.1) : ∀ᶠ y in 𝓝 x, 0 < y.1 :=
  (isOpen_lt continuous_const continuous_fst).mem_nhds hx

lemma hdd_contDiffAt {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {ψ : ℝ × ℝ → ℝ}
    (hψ : NiceStream c ψ) {x : Coord} (hx : 0 < x.1) :
    ContDiffAt ℝ ∞ (heatStreamH ν ψ) x :=
  (heatConvSmooth c ν ψ hc hν hψ).contDiffAt (hdd_nhds hx)

/-- `heatStreamH` is linear in the datum under a constant factor. -/
lemma hdd_heat_smul (ν a : ℝ) (g : ℝ × ℝ → ℝ) (x : Coord) :
    heatStreamH ν (fun p => a * g p) x = a * heatStreamH ν g x := by
  unfold heatStreamH
  split_ifs with h
  · rw [← integral_const_mul]
    congr 1
    funext w
    dsimp only
    ring
  · simp

lemma hdd_abs_scale {ν : ℝ} (hν : 0 < ν) (g : ℝ × ℝ → ℝ) (x : Coord) :
    |heatStreamH ν (fun p => ν * g p) x| = ν * |heatStreamH ν g x| := by
  rw [hdd_heat_smul, abs_mul, abs_of_pos hν]

lemma hdd_scale_sum {ν : ℝ} (hν : 0 < ν) (L : List (ℝ × ℝ → ℝ)) (x : Coord) :
    ((L.map (fun g => fun p => ν * g p)).map (fun g => |heatStreamH ν g x|)).sum =
      ν * (L.map (fun g => |heatStreamH ν g x|)).sum := by
  induction L with
  | nil => simp
  | cons g L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [hdd_abs_scale hν]
    ring

/-- `cpd 1` of `cpd 1` of a heat flow is the heat flow of `∂_q²ζ`, on `τ > 0`. -/
lemma hdd_cpd_cpd1 {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    {y : Coord} (hy : 0 < y.1) :
    cpd 1 (cpd 1 (heatStreamH ν ζ)) y = heatStreamH ν (qDer (qDer ζ)) y := by
  have hq : NiceStream c (qDer ζ) := (niceStreamClosure c ζ ζ 0 hζ hζ).1
  have hev : cpd 1 (heatStreamH ν ζ) =ᶠ[𝓝 y] heatStreamH ν (qDer ζ) :=
    (hdd_ev hy).mono fun z hz => (heatConvCpd c ν ζ hc hν hζ z hz).1
  have h1 : fderiv ℝ (cpd 1 (heatStreamH ν ζ)) y = fderiv ℝ (heatStreamH ν (qDer ζ)) y :=
    hev.fderiv_eq
  show fderiv ℝ (cpd 1 (heatStreamH ν ζ)) y (cdir 1) = heatStreamH ν (qDer (qDer ζ)) y
  rw [h1]
  exact (heatConvCpd c ν (qDer ζ) hc hν hq y hy).1

lemma hdd_cpd_cpd2 {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    {y : Coord} (hy : 0 < y.1) :
    cpd 2 (cpd 2 (heatStreamH ν ζ)) y = heatStreamH ν (etaDer (etaDer ζ)) y := by
  have he : NiceStream c (etaDer ζ) := (niceStreamClosure c ζ ζ 0 hζ hζ).2.1
  have hev : cpd 2 (heatStreamH ν ζ) =ᶠ[𝓝 y] heatStreamH ν (etaDer ζ) :=
    (hdd_ev hy).mono fun z hz => (heatConvCpd c ν ζ hc hν hζ z hz).2
  have h1 : fderiv ℝ (cpd 2 (heatStreamH ν ζ)) y = fderiv ℝ (heatStreamH ν (etaDer ζ)) y :=
    hev.fderiv_eq
  show fderiv ℝ (cpd 2 (heatStreamH ν ζ)) y (cdir 2) = heatStreamH ν (etaDer (etaDer ζ)) y
  rw [h1]
  exact (heatConvCpd c ν (etaDer ζ) hc hν he y hy).2

/-- The `η`-free `τ`-derivative of a heat flow is `ν` times its second spatial derivatives. -/
lemma hdd_cpd0 {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    {y : Coord} (hy : 0 < y.1) :
    cpd 0 (heatStreamH ν ζ) y =
      ν * (heatStreamH ν (qDer (qDer ζ)) y + heatStreamH ν (etaDer (etaDer ζ)) y) := by
  rw [heatConvEq c ν ζ hc hν hζ y hy, hdd_cpd_cpd1 hc hν hζ hy, hdd_cpd_cpd2 hc hν hζ hy]

lemma hdd_norm_eventually_bound {ν : ℝ} (hν : 0 < ν) {A B : Coord → ℝ} {n : ℕ} {x : Coord}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x) :
    ‖iteratedFDeriv ℝ n (fun y => ν * (A y + B y)) x‖ ≤
      ν * (‖iteratedFDeriv ℝ n A x‖ + ‖iteratedFDeriv ℝ n B x‖) := by
  have hfun : (fun y => ν * (A y + B y)) = fun y => ν • (A y + B y) := by
    funext y
    rw [smul_eq_mul]
  rw [hfun, iteratedFDeriv_const_smul_apply' ((hdd_ca n hA).add (hdd_ca n hB)),
    hdd_iter_add (hdd_ca n hA) (hdd_ca n hB), norm_smul,
    Real.norm_of_nonneg hν.le]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hν.le

/-- Finite families of nice streams dominating the `n`-th derivative of a heat flow. -/
def hddList (c ν : ℝ) (n : ℕ) (ζ : ℝ × ℝ → ℝ) : Prop :=
  ∃ L : List (ℝ × ℝ → ℝ), (∀ g ∈ L, NiceStream c g) ∧
    ∀ x : Coord, 0 < x.1 →
      ‖iteratedFDeriv ℝ n (heatStreamH ν ζ) x‖ ≤ (L.map fun g => |heatStreamH ν g x|).sum

lemma hddList_zero {c ν : ℝ} (ζ : ℝ × ℝ → ℝ) (hζ : NiceStream c ζ) : hddList c ν 0 ζ := by
  refine ⟨[ζ], ?_, fun x _ => ?_⟩
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    exact hζ
  · rw [norm_iteratedFDeriv_zero]
    simp [Real.norm_eq_abs]

lemma hddList_succ {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) (n : ℕ)
    (ih : ∀ ζ : ℝ × ℝ → ℝ, NiceStream c ζ → hddList c ν n ζ) (ζ : ℝ × ℝ → ℝ)
    (hζ : NiceStream c ζ) : hddList c ν (n + 1) ζ := by
  have hq : ∀ ψ : ℝ × ℝ → ℝ, NiceStream c ψ → NiceStream c (qDer ψ) :=
    fun ψ h => (niceStreamClosure c ψ ψ 0 h h).1
  have he : ∀ ψ : ℝ × ℝ → ℝ, NiceStream c ψ → NiceStream c (etaDer ψ) :=
    fun ψ h => (niceStreamClosure c ψ ψ 0 h h).2.1
  obtain ⟨L1, hL1, b1⟩ := ih (qDer ζ) (hq ζ hζ)
  obtain ⟨L2, hL2, b2⟩ := ih (etaDer ζ) (he ζ hζ)
  obtain ⟨LA, hLA, bA⟩ := ih (qDer (qDer ζ)) (hq _ (hq ζ hζ))
  obtain ⟨LB, hLB, bB⟩ := ih (etaDer (etaDer ζ)) (he _ (he ζ hζ))
  refine ⟨L1 ++ L2 ++ (LA ++ LB).map (fun g => fun p => ν * g p), ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with (hg | hg) | ⟨h, hh, rfl⟩
    · exact hL1 g hg
    · exact hL2 g hg
    · rcases hh with hh | hh
      · exact nsc_smul ν (hLA h hh)
      · exact nsc_smul ν (hLB h hh)
  · intro x hx
    have hD : ContDiffAt ℝ ∞ (fun y => fderiv ℝ (heatStreamH ν ζ) y) x :=
      ContDiffAt.fderiv_right (hdd_contDiffAt hc hν hζ hx) (by simp)
    rw [← norm_iteratedFDeriv_fderiv]
    refine (hdd_split hD n).trans ?_
    rw [Fin.sum_univ_three]
    -- the `τ`-derivative
    have hev0 : cpd 0 (heatStreamH ν ζ) =ᶠ[𝓝 x]
        fun y => ν * (heatStreamH ν (qDer (qDer ζ)) y + heatStreamH ν (etaDer (etaDer ζ)) y) :=
      (hdd_ev hx).mono fun y hy => hdd_cpd0 hc hν hζ hy
    have hA : ContDiffAt ℝ ∞ (heatStreamH ν (qDer (qDer ζ))) x :=
      hdd_contDiffAt hc hν (hq _ (hq ζ hζ)) hx
    have hB : ContDiffAt ℝ ∞ (heatStreamH ν (etaDer (etaDer ζ))) x :=
      hdd_contDiffAt hc hν (he _ (he ζ hζ)) hx
    have h0 : ‖iteratedFDeriv ℝ n (cpd 0 (heatStreamH ν ζ)) x‖ ≤
        ν * (LA.map (fun g => |heatStreamH ν g x|)).sum +
          ν * (LB.map (fun g => |heatStreamH ν g x|)).sum := by
      rw [(hev0.iteratedFDeriv ℝ n).eq_of_nhds]
      refine (hdd_norm_eventually_bound hν hA hB).trans ?_
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (add_le_add (bA x hx) (bB x hx)) hν.le
    have hev1 : cpd 1 (heatStreamH ν ζ) =ᶠ[𝓝 x] heatStreamH ν (qDer ζ) :=
      (hdd_ev hx).mono fun y hy => (heatConvCpd c ν ζ hc hν hζ y hy).1
    have hev2 : cpd 2 (heatStreamH ν ζ) =ᶠ[𝓝 x] heatStreamH ν (etaDer ζ) :=
      (hdd_ev hx).mono fun y hy => (heatConvCpd c ν ζ hc hν hζ y hy).2
    have h1 : ‖iteratedFDeriv ℝ n (cpd 1 (heatStreamH ν ζ)) x‖ ≤
        (L1.map (fun g => |heatStreamH ν g x|)).sum := by
      rw [(hev1.iteratedFDeriv ℝ n).eq_of_nhds]
      exact b1 x hx
    have h2 : ‖iteratedFDeriv ℝ n (cpd 2 (heatStreamH ν ζ)) x‖ ≤
        (L2.map (fun g => |heatStreamH ν g x|)).sum := by
      rw [(hev2.iteratedFDeriv ℝ n).eq_of_nhds]
      exact b2 x hx
    simp only [List.map_append, List.sum_append, hdd_scale_sum hν]
    linarith

lemma hdd_all {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) (n : ℕ) :
    ∀ ζ : ℝ × ℝ → ℝ, NiceStream c ζ → hddList c ν n ζ := by
  induction n with
  | zero => exact fun ζ hζ => hddList_zero ζ hζ
  | succ n ih => exact fun ζ hζ => hddList_succ hc hν n ih ζ hζ

/-- **Leaf `PartII-b:T11/3/8`** (pointwise domination of the Fréchet derivatives of the heat flow
by heat flows of nice streams). -/
theorem heatDerivDomination : UnforcedLeray.Short.IIb.HeatDerivDomination := by
  intro c ν ζ n hc hν hζ
  obtain ⟨L, hL, hb⟩ := hdd_all hc hν n ζ hζ
  refine ⟨L.length, fun j => L.get j, fun j => hL _ (List.get_mem L j), fun x hx => ?_⟩
  refine (hb x hx).trans (le_of_eq ?_)
  conv_lhs => rw [← List.ofFn_get L]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

end UnforcedLeray.Short.IIb
