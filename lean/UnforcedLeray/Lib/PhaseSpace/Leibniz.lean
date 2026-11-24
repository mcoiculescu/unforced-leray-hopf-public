import UnforcedLeray.Lib.PhaseSpace.Graph
import UnforcedLeray.Lib.PhaseSpace.CutoffCalc
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Distributional commutator of `∂ⱼ` with `A₀` (INF25 T25.12; blueprint B0413)

Tex lines 5750–5753 (B0413): for `z_j = ∂ⱼ w`, `∂ⱼ A₀ w = (A₀ − ½) z_j`, where
`A₀ = T₀ − νΔ − ½` (tex 5161, 5208, 3600) and `T₀ = ∂_τ − ½ y·∇`. The identity comes from
`[∂ⱼ, y·∇] = ∂ⱼ` and `[∂ⱼ, Δ] = 0`, and it is used distributionally in the derivative
induction of B0694 (tex 5812–5829).

On phase tests the transposed operators satisfy (`dy_driftT`, `dy_lapT`)

  `∂ⱼ (T₀ᵗ Φ) = T₀ᵗ (∂ⱼ Φ) + ½ ∂ⱼ Φ`,   `∂ⱼ (ΔΦ) = Δ (∂ⱼ Φ)`,

using symmetry of second derivatives of smooth tests. `freeGraph_commutator_deriv` is
B0413 for a graph triple `(w, νΔw, T₀w)` and a distributional derivative `z = ∂ⱼ w ∈ Y_q`:
the distribution `∂ⱼ(A₀ w)` equals the distribution `(A₀ − ½) z`, whose transpose on tests
is `T₀ᵗ − νΔ − 1`. No graph regularity of `z` is assumed. When `z` is itself in the graph,
`freeGraph_commutator_deriv'` states the identity inside `Y_q`.

Status: the D^α induction (B0694) and `HasPhaseOp.mul_smooth` of T25.12 are not built here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.PhaseSpace

section Calculus

variable {Φ : ℝ × Space → CVec3}

theorem fderiv_apply_formula (hΦ : ContDiff ℝ ∞ Φ) (v w p : ℝ × Space) :
    fderiv ℝ (fun p => fderiv ℝ Φ p w) p v = fderiv ℝ (fderiv ℝ Φ) p v w := by
  have hd : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ Φ y w) ((fderiv ℝ (fderiv ℝ Φ) p).flip w) p := by
    simpa using (hd p).hasFDerivAt.clm_apply (hasFDerivAt_const w p)
  rw [hx.fderiv]
  rfl

/-- Symmetry of second derivatives of a smooth phase function. -/
theorem fderiv_apply_comm (hΦ : ContDiff ℝ ∞ Φ) (v w p : ℝ × Space) :
    fderiv ℝ (fun p => fderiv ℝ Φ p w) p v = fderiv ℝ (fun p => fderiv ℝ Φ p v) p w := by
  rw [fderiv_apply_formula hΦ v w p, fderiv_apply_formula hΦ w v p]
  exact (hΦ.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

theorem dy_dy_comm (hΦ : ContDiff ℝ ∞ Φ) (j k : Fin 3) : dy j (dy k Φ) = dy k (dy j Φ) :=
  funext fun p => fderiv_apply_comm hΦ _ _ p

theorem dy_dτ_comm (hΦ : ContDiff ℝ ∞ Φ) (j : Fin 3) : dy j (dτ Φ) = dτ (dy j Φ) :=
  funext fun p => fderiv_apply_comm hΦ _ _ p

theorem dy_sum {ι : Type*} (s : Finset ι) {G : ι → ℝ × Space → CVec3}
    (hG : ∀ i ∈ s, Differentiable ℝ (G i)) (j : Fin 3) :
    dy j (∑ i ∈ s, G i) = ∑ i ∈ s, dy j (G i) := by
  funext p
  simp only [dy, Finset.sum_apply]
  rw [fderiv_sum fun i hi => (hG i hi) p]
  simp

theorem dy_smul {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (c : ℝ) (j : Fin 3) :
    dy j (c • G) = c • dy j G := by
  funext p
  simp [dy, fderiv_const_smul (hG p) c]

theorem dy_neg (G : ℝ × Space → CVec3) (j : Fin 3) : dy j (-G) = -dy j G := by
  funext p
  simp [dy, fderiv_neg]

theorem dτ_neg (G : ℝ × Space → CVec3) : dτ (-G) = -dτ G := by
  funext p
  simp [dτ, fderiv_neg]

theorem lapT_neg (G : ℝ × Space → CVec3) : lapT (-G) = -lapT G := by
  funext p
  simp [lapT, dy_neg, Finset.sum_neg_distrib]

theorem driftT_neg (G : ℝ × Space → CVec3) : driftT (-G) = -driftT G := by
  funext p
  simp only [driftT, radialT, dτ_neg, dy_neg, Pi.neg_apply, smul_neg, Finset.sum_neg_distrib]
  abel

theorem sd_coord (j k : Fin 3) :
    sd j (fun y : Space => y k) = fun _ => if k = j then 1 else 0 := by
  funext y
  have h : fderiv ℝ (fun y : Space => y k) y = (EuclideanSpace.proj k : Space →L[ℝ] ℝ) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).fderiv
  simp [sd, h, coordinateVector, EuclideanSpace.single_apply]

theorem contDiff_coord (k : Fin 3) : ContDiff ℝ ∞ (fun y : Space => y k) :=
  (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff

theorem radialT_eq (G : ℝ × Space → CVec3) :
    radialT G = ∑ k : Fin 3, mulT (fun y : Space => y k) (dy k G) := by
  funext p
  simp [radialT, mulT, Finset.sum_apply]

theorem contDiff_radialT (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (radialT Φ) := by
  show ContDiff ℝ ∞ (fun p : ℝ × Space => ∑ k : Fin 3, (p.2 k) • dy k Φ p)
  exact ContDiff.sum fun k _ => ((contDiff_coord k).comp contDiff_snd).smul (contDiff_dy hΦ k)

theorem contDiff_lapT (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (lapT Φ) :=
  ContDiff.sum fun k _ => contDiff_dy (contDiff_dy hΦ k) k

/-- `∂ⱼ (y·∇Φ) = y·∇(∂ⱼΦ) + ∂ⱼΦ`. -/
theorem dy_radialT (hΦ : ContDiff ℝ ∞ Φ) (j : Fin 3) :
    dy j (radialT Φ) = radialT (dy j Φ) + dy j Φ := by
  have hd : ∀ {b : Space → ℝ}, ContDiff ℝ ∞ b → Differentiable ℝ b :=
    fun hb => hb.differentiable (by simp)
  have hD : ∀ {G : ℝ × Space → CVec3}, ContDiff ℝ ∞ G → Differentiable ℝ G :=
    fun hG => hG.differentiable (by simp)
  rw [radialT_eq, radialT_eq,
    dy_sum _ (fun k _ => hD (contDiff_mulT (contDiff_coord k) (contDiff_dy hΦ k))) j]
  funext p
  simp only [Finset.sum_apply, Pi.add_apply]
  have hk : ∀ k : Fin 3, dy j (mulT (fun y : Space => y k) (dy k Φ)) p =
      mulT (fun y : Space => y k) (dy k (dy j Φ)) p +
        (if k = j then dy k Φ p else 0) := by
    intro k
    rw [dy_mulT (hd (contDiff_coord k)) (hD (contDiff_dy hΦ k)), dy_dy_comm hΦ j k, sd_coord]
    simp only [Pi.add_apply, mulT]
    split_ifs <;> simp
  simp only [hk, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `∂ⱼ (T₀ᵗ Φ) = T₀ᵗ (∂ⱼ Φ) + ½ ∂ⱼ Φ`. -/
theorem dy_driftT (hΦ : ContDiff ℝ ∞ Φ) (j : Fin 3) :
    dy j (driftT Φ) = driftT (dy j Φ) + (1 / 2 : ℝ) • dy j Φ := by
  have hD : ∀ {G : ℝ × Space → CVec3}, ContDiff ℝ ∞ G → Differentiable ℝ G :=
    fun hG => hG.differentiable (by simp)
  have hform : ∀ G : ℝ × Space → CVec3,
      driftT G = -dτ G + (1 / 2 : ℝ) • radialT G + (3 / 2 : ℝ) • G := by
    intro G
    funext p
    simp [driftT]
  rw [hform Φ, hform (dy j Φ),
    dy_add ((hD (contDiff_dτ hΦ)).neg.add ((hD (contDiff_radialT hΦ)).const_smul _))
      ((hD hΦ).const_smul _),
    dy_add (hD (contDiff_dτ hΦ)).neg ((hD (contDiff_radialT hΦ)).const_smul _),
    dy_neg, dy_smul (hD (contDiff_radialT hΦ)), dy_smul (hD hΦ), dy_dτ_comm hΦ,
    dy_radialT hΦ]
  funext p
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply]
  module

/-- `∂ⱼ (ΔΦ) = Δ (∂ⱼ Φ)`. -/
theorem dy_lapT (hΦ : ContDiff ℝ ∞ Φ) (j : Fin 3) : dy j (lapT Φ) = lapT (dy j Φ) := by
  have hD : ∀ {G : ℝ × Space → CVec3}, ContDiff ℝ ∞ G → Differentiable ℝ G :=
    fun hG => hG.differentiable (by simp)
  have hform : ∀ G : ℝ × Space → CVec3, lapT G = ∑ k : Fin 3, dy k (dy k G) := by
    intro G
    funext p
    simp [lapT, Finset.sum_apply]
  rw [hform Φ, hform (dy j Φ),
    dy_sum _ (fun k _ => hD (contDiff_dy (contDiff_dy hΦ k) k)) j]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dy_dy_comm (contDiff_dy hΦ k) j k, dy_dy_comm hΦ j k]

end Calculus

/-! ### The distributional commutator (B0413) -/

section Commutator

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- **B0413** (tex 5750–5753). Let `(w, νΔw, T₀w) = (w, a, b)` be in the free graph and let
`z = ∂ⱼ w ∈ Y_q` in distributions. Then `∂ⱼ (A₀ w) = (A₀ − ½) z` in distributions, with
`A₀ w = b − a − ½ w` and `A₀ = T₀ − νΔ − ½`: for every phase test `Φ`,

  `⟪−∂ⱼΦ, A₀ w⟫ = ⟪T₀ᵗΦ − νΔΦ − Φ, z⟫`. -/
theorem freeGraph_commutator_deriv {ν : ℝ} {w a b z : Yq P q}
    (hw : (w, a, b) ∈ freeGraph P ν q) (j : Fin 3)
    (hz : HasPhaseOp (fun Φ => -dy j Φ) w z) (Φ : ℝ × Space → CVec3)
    (hΦ : IsPhaseTest P Φ) :
    phasePair P q (-dy j Φ) (b - a - (1 / 2 : ℂ) • w) =
      phasePair P q (driftT Φ - nuLapT ν Φ - Φ) z := by
  have hdj : IsPhaseTest P (-dy j Φ) := (hΦ.dy j).neg
  have hD := hΦ.driftT
  have hL : IsPhaseTest P (nuLapT ν Φ) := hΦ.lapT.const_smul ν
  -- test identities
  have t1 : driftT (-dy j Φ) = -dy j (driftT Φ) + (1 / 2 : ℝ) • dy j Φ := by
    rw [driftT_neg, dy_driftT hΦ.smooth j]
    abel
  have t2 : nuLapT ν (-dy j Φ) = -dy j (nuLapT ν Φ) := by
    simp only [nuLapT]
    rw [lapT_neg, dy_smul ((contDiff_lapT hΦ.smooth).differentiable (by simp)), dy_lapT hΦ.smooth]
    simp
  -- the graph identities with the test `-∂ⱼΦ`
  have g1 := hw.2 (-dy j Φ) hdj
  have g2 := hw.1 (-dy j Φ) hdj
  rw [t1] at g1
  rw [t2] at g2
  -- the derivative identity with the tests `T₀ᵗΦ`, `νΔΦ`, `Φ`
  have d1 := hz (driftT Φ) hD
  have d2 := hz (nuLapT ν Φ) hL
  have d3 := hz Φ hΦ
  simp only at d1 d2 d3
  have hY := phasePair_neg (q := q) (hΦ.dy j) w
  rw [map_sub, map_sub, map_smul, smul_eq_mul, ← g1, ← g2,
    phasePair_add (hD.dy j).neg ((hΦ.dy j).const_smul (1 / 2 : ℝ)),
    phasePair_real_smul (hΦ.dy j), phasePair_sub (hD.sub hL) hΦ, phasePair_sub hD hL,
    ← d1, ← d2, ← d3, hY]
  push_cast
  ring

/-- **B0413 inside `Y_q`.** When `z = ∂ⱼ w` is itself in the graph, `(z, a', b')`, the
commutator identity holds with both sides in `Y_q`: `∂ⱼ (A₀ w) = A₀ z − ½ z`, where
`A₀ z = b' − a' − ½ z` (the form used in the derivative induction of B0694). -/
theorem freeGraph_commutator_deriv' {ν : ℝ} {w a b z a' b' : Yq P q}
    (hw : (w, a, b) ∈ freeGraph P ν q) (hzG : (z, a', b') ∈ freeGraph P ν q) (j : Fin 3)
    (hz : HasPhaseOp (fun Φ => -dy j Φ) w z) :
    HasPhaseOp (fun Φ => -dy j Φ) (b - a - (1 / 2 : ℂ) • w)
      (b' - a' - (1 / 2 : ℂ) • z - (1 / 2 : ℂ) • z) := by
  intro Φ hΦ
  have hL : IsPhaseTest P (nuLapT ν Φ) := hΦ.lapT.const_smul ν
  simp only
  rw [freeGraph_commutator_deriv hw j hz Φ hΦ, phasePair_sub (hΦ.driftT.sub hL) hΦ,
    phasePair_sub hΦ.driftT hL, hzG.2 Φ hΦ, hzG.1 Φ hΦ]
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

end Commutator

end UnforcedLeray.PhaseSpace
