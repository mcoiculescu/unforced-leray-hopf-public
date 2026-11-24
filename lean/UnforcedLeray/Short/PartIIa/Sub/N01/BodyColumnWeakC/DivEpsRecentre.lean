import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_2_3
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnWeakC.InnerZetaUnwind

/-!
# `PartII-a:N01/9/2/3/3`: `DivEpsRecentre`

Source `the November 2 reference manuscript` lines 1669-1689.
`G = s·divEps 0 M` (a.e. for `measureH`) transports, by `cellPtInv`, to the recentred chart; the
`c`-periodicity of `M` in `q` gives `divEps 0 M (cellPtInv x) = divEps 0 M x` (at `ε = 0` only the
`q`- and `η`-derivatives enter `divEps`), and dividing by `s > 0` finishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure weightH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (cellPtInv measurable_cellPtInv)

theorem fderiv_qshift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    {g : Profile → E} (hg : ∀ p : Profile, g (p.1, p.2.1 + c, p.2.2) = g p) (p : Profile)
    (w : ℝ × (ℝ × ℝ)) :
    fderiv ℝ g (p.1, p.2.1 + c, p.2.2) w = fderiv ℝ g p w := by
  have hfun : (fun t : Profile => g (t + (0, (c, 0)))) = g := by
    funext t
    have e : t + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) = (t.1, t.2.1 + c, t.2.2) := by
      ext <;> simp
    rw [e]
    exact hg t
  have h1 := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := p) ((0 : ℝ), ((c : ℝ), (0 : ℝ)))
  rw [hfun] at h1
  have e : p + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) = (p.1, p.2.1 + c, p.2.2) := by
    ext <;> simp
  rw [e] at h1
  rw [← h1]

theorem divEps_qshift {c : ℝ} {M : Profile → TensorVal}
    (hM : ∀ p : Profile, M (p.1, p.2.1 + c, p.2.2) = M p) (p : Profile) :
    divEps 0 M (p.1, p.2.1 + c, p.2.2) = divEps 0 M p := by
  have hk : ∀ k : Fin 4, ∀ q : Profile, (fun x : Profile => M x k) (q.1, q.2.1 + c, q.2.2) =
      (fun x : Profile => M x k) q := fun k q => by
    dsimp only
    rw [hM q]
  have a0 := fderiv_qshift (g := fun x : Profile => M x 0) (c := c) (hk 0) p (0, 1, 0)
  have a1 := fderiv_qshift (g := fun x : Profile => M x 1) (c := c) (hk 1) p (0, 1, 0)
  have b1 := fderiv_qshift (g := fun x : Profile => M x 1) (c := c) (hk 1) p (0, 0, 1)
  have b2 := fderiv_qshift (g := fun x : Profile => M x 2) (c := c) (hk 2) p (0, 0, 1)
  unfold divEps opQ pdQ pdEta
  simp only [zero_smul, sub_zero, Complex.ofReal_zero, zero_mul, a0, a1, b1, b2]

theorem divEps_cellPtInv {c : ℝ} {M : Profile → TensorVal}
    (hM : ∀ p : Profile, M (p.1, p.2.1 + c, p.2.2) = M p) (x : Chart) :
    divEps 0 M (cellPtInv c x) = divEps 0 M x := by
  obtain ⟨s, q, η⟩ := x
  by_cases h : 0 < q
  · have e : cellPtInv c (s, (q, η)) = (s, (q, η)) := by
      simp [cellPtInv, h]
    rw [e]
  · have e : cellPtInv c (s, (q, η)) = (s, (q + c, η)) := by
      simp [cellPtInv, h]
    rw [e]
    exact divEps_qshift hM (s, (q, η))

theorem divEpsRecentre : UnforcedLeray.Short.PartIIa.N01.DivEpsRecentre := by
  intro c hc M hM G hG
  have hw : Measurable weightH := UnforcedLeray.B0220.measurable_weightH
  have hcell_pos : ∀ᵐ a ∂(cellMeasure c), 0 < a.1 := by
    unfold cellMeasure
    filter_upwards [ae_restrict_mem (UnforcedLeray.B0220.measurableSet_cell c)] with a ha
    exact ha.1
  have hcell_ne : ∀ᵐ a ∂(cellMeasure c), weightH a ≠ 0 := by
    filter_upwards [hcell_pos] with a ha
    unfold weightH
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ha _)).ne'
  have hac : cellMeasure c ≪ measureH c := withDensity_absolutelyContinuous' hw.aemeasurable hcell_ne
  have hGc : ∀ᵐ y ∂(cellMeasure c), (G : Profile → MeridC) y = (y.1 : ℂ) • divEps 0 M y :=
    hac.ae_le hG
  have hGchart : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)),
      (G : Profile → MeridC) (cellPtInv c x) = ((cellPtInv c x).1 : ℂ) • divEps 0 M (cellPtInv c x) :=
    ae_of_ae_map (measurable_cellPtInv c).aemeasurable
      (by rw [cellPtInv_map hc]; exact hGc)
  have hpos : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)), 0 < x.1 :=
    (ae_restrict_mem (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ))).mono
      fun x hx => hx.1
  filter_upwards [hGchart, hpos] with x h1 h2 i
  have hx : (x.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h2.ne'
  have hdiv := divEps_cellPtInv hM.periodic x
  show (G : Profile → MeridC) (cellPtInv c x) i / (x.1 : ℂ) = divEps 0 M x i
  rw [h1, hdiv]
  exact mul_div_cancel_left₀ _ hx

end UnforcedLeray.Short.PartIIa.N01
