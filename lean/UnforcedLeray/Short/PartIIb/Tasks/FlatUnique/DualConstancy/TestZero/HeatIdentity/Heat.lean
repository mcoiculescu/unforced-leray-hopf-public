import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.HeatIdentity.Calc

/-!
# Helper for `PartII-b:T11/2/2/3`: the time-reversed heat solution `G(σ,·) = H(s-σ,·)`

On the slab `W = (0,s) × ℝ²`: `G` is smooth and `G_σ + ν Δ G = 0`, and the same holds for every
partial derivative `∂_d G`, `d ∈ {1,2}` (heat identity differentiated).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- the open slab `0 < σ < s`. -/
def dtW (s : ℝ) : Set Coord := Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))

theorem isOpen_dtW (s : ℝ) : IsOpen (dtW s) := isOpen_Ioo.prod isOpen_univ

/-- the time reversal `σ ↦ s - σ`. -/
def dtPhi (s : ℝ) (y : Coord) : Coord := (s - y.1, y.2)

/-- `G(σ,q,η) = H(s - σ, q, η)`. -/
def dtG (H : Coord → ℝ) (s : ℝ) (y : Coord) : ℝ := H (dtPhi s y)

/-- the linear part of `dtPhi`. -/
def dtL : Coord →L[ℝ] Coord :=
  (-(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

theorem hasFDerivAt_dtPhi (s : ℝ) (y : Coord) : HasFDerivAt (dtPhi s) dtL y :=
  ((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).const_sub s).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := y))

theorem chain_s {K : Coord → ℝ} {s : ℝ} {y : Coord} (hK : DifferentiableAt ℝ K (dtPhi s y)) :
    cpd 0 (fun z => K (dtPhi s z)) y = - cpd 0 K (dtPhi s y) := by
  have h : HasFDerivAt (fun z => K (dtPhi s z)) ((fderiv ℝ K (dtPhi s y)).comp dtL) y :=
    hK.hasFDerivAt.comp y (hasFDerivAt_dtPhi s y)
  have : dtL (cdir 0) = -(cdir 0) := by
    ext <;> simp [dtL, cdir]
  rw [cpd, h.fderiv]
  simp [this, cpd]

theorem chain_q {K : Coord → ℝ} {s : ℝ} {y : Coord} (hK : DifferentiableAt ℝ K (dtPhi s y)) :
    cpd 1 (fun z => K (dtPhi s z)) y = cpd 1 K (dtPhi s y) := by
  have h : HasFDerivAt (fun z => K (dtPhi s z)) ((fderiv ℝ K (dtPhi s y)).comp dtL) y :=
    hK.hasFDerivAt.comp y (hasFDerivAt_dtPhi s y)
  have : dtL (cdir 1) = cdir 1 := by
    ext <;> simp [dtL, cdir]
  rw [cpd, h.fderiv]
  simp [this, cpd]

theorem chain_e {K : Coord → ℝ} {s : ℝ} {y : Coord} (hK : DifferentiableAt ℝ K (dtPhi s y)) :
    cpd 2 (fun z => K (dtPhi s z)) y = cpd 2 K (dtPhi s y) := by
  have h : HasFDerivAt (fun z => K (dtPhi s z)) ((fderiv ℝ K (dtPhi s y)).comp dtL) y :=
    hK.hasFDerivAt.comp y (hasFDerivAt_dtPhi s y)
  have : dtL (cdir 2) = cdir 2 := by
    ext <;> simp [dtL, cdir]
  rw [cpd, h.fderiv]
  simp [this, cpd]

theorem dtPhi_mem {s : ℝ} {y : Coord} (hy : y ∈ dtW s) :
    dtPhi s y ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
  refine ⟨?_, trivial⟩
  have := hy.1.2
  show 0 < s - y.1
  linarith

theorem dtG_contDiffOn {H : Coord → ℝ} {s : ℝ}
    (hH : ContDiffOn ℝ ∞ H (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) :
    ContDiffOn ℝ ∞ (dtG H s) (dtW s) := by
  have hφ : ContDiff ℝ ∞ (dtPhi s) := by
    unfold dtPhi
    exact (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  exact hH.comp hφ.contDiffOn (fun y hy => dtPhi_mem hy)

/-- `G_σ + ν Δ G = 0` on the slab. -/
theorem dtG_heat {c ν r' : ℝ} {H : Coord → ℝ} {s : ℝ} (hH : HeatSol c ν r' H) :
    ∀ y ∈ dtW s, cpd 0 (dtG H s) y +
      ν * (cpd 1 (cpd 1 (dtG H s)) y + cpd 2 (cpd 2 (dtG H s)) y) = 0 := by
  have hΩ : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hd : ∀ (K : Coord → ℝ), ContDiffOn ℝ ∞ K (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) →
      ∀ y ∈ dtW s, DifferentiableAt ℝ K (dtPhi s y) := fun K hK y hy =>
    (hK.contDiffAt (hΩ.mem_nhds (dtPhi_mem hy))).differentiableAt (by norm_num)
  intro y hy
  have hq : ∀ z ∈ dtW s, cpd 1 (dtG H s) z = cpd 1 H (dtPhi s z) := fun z hz =>
    chain_q (hd H hH.smooth z hz)
  have he : ∀ z ∈ dtW s, cpd 2 (dtG H s) z = cpd 2 H (dtPhi s z) := fun z hz =>
    chain_e (hd H hH.smooth z hz)
  have hqq : cpd 1 (cpd 1 (dtG H s)) y = cpd 1 (cpd 1 H) (dtPhi s y) := by
    rw [cpd_congr_on (isOpen_dtW s) hq 1 y hy]
    exact chain_q (K := cpd 1 H) (hd _ (cpd_contDiffOn' hΩ hH.smooth 1) y hy)
  have hee : cpd 2 (cpd 2 (dtG H s)) y = cpd 2 (cpd 2 H) (dtPhi s y) := by
    rw [cpd_congr_on (isOpen_dtW s) he 2 y hy]
    exact chain_e (K := cpd 2 H) (hd _ (cpd_contDiffOn' hΩ hH.smooth 2) y hy)
  have hs0 : cpd 0 (dtG H s) y = - cpd 0 H (dtPhi s y) := chain_s (hd H hH.smooth y hy)
  rw [hs0, hqq, hee, hH.heat _ (dtPhi_mem hy)]
  ring

/-- the heat identity differentiated: `(∂_d G)_σ + νΔ(∂_d G) = 0`. -/
theorem dtG_heat_d {c ν r' : ℝ} {H : Coord → ℝ} {s : ℝ} (hH : HeatSol c ν r' H) (d : Fin 3) :
    ∀ y ∈ dtW s, cpd 0 (cpd d (dtG H s)) y +
      ν * (cpd 1 (cpd 1 (cpd d (dtG H s))) y + cpd 2 (cpd 2 (cpd d (dtG H s))) y) = 0 := by
  have hW := isOpen_dtW s
  have hG := dtG_contDiffOn (s := s) hH.smooth
  have hc : ∀ j, ContDiffOn ℝ ∞ (cpd j (dtG H s)) (dtW s) := fun j => cpd_contDiffOn' hW hG j
  have hcc : ∀ j k, ContDiffOn ℝ ∞ (cpd j (cpd k (dtG H s))) (dtW s) := fun j k =>
    cpd_contDiffOn' hW (hc k) j
  intro y hy
  have hdiff : ∀ {f : Coord → ℝ}, ContDiffOn ℝ ∞ f (dtW s) → DifferentiableAt ℝ f y :=
    fun hf => (hf.contDiffAt (hW.mem_nhds hy)).differentiableAt (by norm_num)
  -- the heat identity as a function identity on `W`
  have hz : ∀ z ∈ dtW s, (fun w => cpd 0 (dtG H s) w +
      ν * (cpd 1 (cpd 1 (dtG H s)) w + cpd 2 (cpd 2 (dtG H s)) w)) z = (fun _ => (0 : ℝ)) z :=
    fun z hz => dtG_heat hH z hz
  have h0 := cpd_congr_on hW hz d y hy
  have hlin : cpd d (fun w => cpd 0 (dtG H s) w +
      ν * (cpd 1 (cpd 1 (dtG H s)) w + cpd 2 (cpd 2 (dtG H s)) w)) y =
      cpd d (cpd 0 (dtG H s)) y + ν * (cpd d (cpd 1 (cpd 1 (dtG H s))) y +
        cpd d (cpd 2 (cpd 2 (dtG H s))) y) := by
    have hA := (hdiff (hc 0)).hasFDerivAt
    have hB := (hdiff (hcc 1 1)).hasFDerivAt
    have hC := (hdiff (hcc 2 2)).hasFDerivAt
    have hT : HasFDerivAt (fun w => cpd 0 (dtG H s) w + ν * (cpd 1 (cpd 1 (dtG H s)) w +
        cpd 2 (cpd 2 (dtG H s)) w)) _ y := hA.add ((hB.add hC).const_mul ν)
    show fderiv ℝ (fun w => cpd 0 (dtG H s) w + ν * (cpd 1 (cpd 1 (dtG H s)) w +
        cpd 2 (cpd 2 (dtG H s)) w)) y (cdir d) = _
    rw [hT.fderiv]
    simp [cpd]
    ring
  have hzero : cpd d (fun _ => (0 : ℝ)) y = 0 := by simp [cpd]
  rw [hzero, hlin] at h0
  -- swap `∂_d` through
  have s0 : cpd d (cpd 0 (dtG H s)) y = cpd 0 (cpd d (dtG H s)) y := cpd_swap hW hG d 0 y hy
  have sk : ∀ k, cpd d (cpd k (cpd k (dtG H s))) y = cpd k (cpd k (cpd d (dtG H s))) y := by
    intro k
    have e1 : cpd d (cpd k (cpd k (dtG H s))) y = cpd k (cpd d (cpd k (dtG H s))) y :=
      cpd_swap hW (hc k) d k y hy
    have e2 : ∀ z ∈ dtW s, cpd d (cpd k (dtG H s)) z = cpd k (cpd d (dtG H s)) z :=
      cpd_swap hW hG d k
    rw [e1, cpd_congr_on hW e2 k y hy]
  rw [s0, sk 1, sk 2] at h0
  exact h0

end UnforcedLeray.Short.IIb
