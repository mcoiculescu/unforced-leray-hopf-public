import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_4
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestFderiv
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.SolenoidalConj
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.T0Conj
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.DivEpsReal

/-!
# `PartIII-b:C/near/delta/8/2/3/4/org/1`: `bodyColumnTransport_of` (source 1650-1656, 1675-1679,
1684-1689)

From the body column of `PartIII-b:C/flatset/col/7` (`BodyColumnFlat`) to the smooth stress column
`BodyColumnTransport`: the real form `R0` of `T0flat` (`Body.bodyForm`) is a body transport; the
real force `G` pins `h = reV G`; the divergence `divEps 0 M` is `q`-periodic and real, so the
hypothesis of `BodyColumnFlat` holds with `f = divEps 0 M`; then the column is transported back
to the cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIa
open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)

/-- `divEps 0 M` is `c`-periodic in `q` for a smooth tensor test `M`. -/
theorem bct_divEps_periodic {c : ℝ} {M : Profile → TensorVal}
    (hM : UnforcedLeray.Short.PartIIa.IsTensorTest c M) :
    ∀ p : Profile, divEps 0 M (p.1, p.2.1 + c, p.2.2) = divEps 0 M p := by
  have hk : ∀ k : Fin 4, ∀ x : Profile,
      M (x.1, x.2.1 + c, x.2.2) k = M x k :=
    fun k x => by rw [hM.periodic x]
  intro p
  have e0 : pdQ (fun y : Profile => M y 0) (p.1, p.2.1 + c, p.2.2) =
      pdQ (fun y : Profile => M y 0) p := by
    unfold pdQ
    rw [ctf_fderiv_periodic (F := fun y : Profile => M y 0) (fun x => hk 0 x) p]
  have e1 : pdEta (fun y : Profile => M y 1) (p.1, p.2.1 + c, p.2.2) =
      pdEta (fun y : Profile => M y 1) p := by
    unfold pdEta
    rw [ctf_fderiv_periodic (F := fun y : Profile => M y 1) (fun x => hk 1 x) p]
  have e2 : pdQ (fun y : Profile => M y 1) (p.1, p.2.1 + c, p.2.2) =
      pdQ (fun y : Profile => M y 1) p := by
    unfold pdQ
    rw [ctf_fderiv_periodic (F := fun y : Profile => M y 1) (fun x => hk 1 x) p]
  have e3 : pdEta (fun y : Profile => M y 2) (p.1, p.2.1 + c, p.2.2) =
      pdEta (fun y : Profile => M y 2) p := by
    unfold pdEta
    rw [ctf_fderiv_periodic (F := fun y : Profile => M y 2) (fun x => hk 2 x) p]
  ext i
  fin_cases i
  · simp [divEps, opQ, e0, e1]
  · simp [divEps, opQ, e2, e3]

/-- A complex number with zero imaginary part is the cast of its real part. -/
theorem bct_re_cast (z : ℂ) (hz : z.im = 0) : ((z.re : ℝ) : ℂ) = z :=
  Complex.ext (by simp) (by simp [hz])

/-- The real part of a meridional vector, applied to a coordinate. -/
theorem bct_merReL_apply (g : MeridC) (i : Fin 2) : (Body.merReL g) i = (g i).re := by
  simp [Body.merReL, Body.merReLin]

/-- A complex meridional vector with zero imaginary parts is the complexification of its real
part. -/
theorem bct_merC_merReL_of_im {g : MeridC} (h : ∀ i, (g i).im = 0) :
    NearInst.merC (Body.merReL g) = g := by
  ext i
  apply Complex.ext
  · simp [NearInst.merC, Body.merReL, Body.merReLin]
  · simp [NearInst.merC, Body.merReL, Body.merReLin, h i]

theorem bodyColumnTransport_of
    (hB : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.BodyColumnFlat) :
    BodyColumnTransport := by
  intro c ν μ hc hν hμ M hM hMr G hG
  have hH : Masked.CellPtH c := Masked.cellPtH_eq c hc
  have hHi : Masked.CellPtInvH c := ct_cellPtInvH c hc
  have hmap : Measure.map (cellPt c) (measureH c) = ENNReal.ofReal c • ageμ c (-3 / 2) := hH
  -- the real form of the body operator is a body transport
  set R0 := Body.bodyForm c hH hHi (PartIIa.T0flat hc ν (μ : ℂ)) with hR0
  have hR : NearInst.IsBodyTransport R0 (PartIIa.T0flat hc ν (μ : ℂ)) :=
    Body.isBodyTransport_bodyForm hH hHi (PartIIa.T0flat hc ν (μ : ℂ))
      (fun g => Body.t0flat_conj Body.solenoidalConj Body.t0Conj hc ν hμ g)
  -- the real force
  have hGreal : ∀ᵐ p ∂measureH c, ∀ i, ((G : Profile → MeridC) p i).im = 0 := by
    filter_upwards [hG] with p hp i
    rw [hp]
    exact Masked.smul_divEps_im 0 M hMr p i
  -- the chart-side real field `h = reV G`
  set h := Body.reV c hHi G with hhdef
  have hreA : ∀ᵐ x ∂ageμ c (-3 / 2), (h : Chart → Merid) x =
      Body.merReL ((G : Profile → MeridC) (Masked.cellPtInv c x)) :=
    Body.reV_ae c hHi G
  -- transport `reV G` to the cell
  have hA : ∀ᵐ y ∂Measure.map (cellPt c) (measureH c), (h : Chart → Merid) y =
      Body.merReL ((G : Profile → MeridC) (Masked.cellPtInv c y)) := by
    rw [hmap]
    exact (Measure.smul_absolutelyContinuous).ae_le hreA
  have hA' : ∀ᵐ p ∂measureH c, (h : Chart → Merid) (cellPt c p) =
      Body.merReL ((G : Profile → MeridC) (Masked.cellPtInv c (cellPt c p))) :=
    ae_of_ae_map (Body.measurable_cellPt' c).aemeasurable hA
  -- `G = merC ∘ h ∘ cellPt` on the cell
  have hGh : (G : Profile → MeridC) =ᵐ[measureH c] fun p =>
      NearInst.merC ((h : Chart → Merid) (cellPt c p)) := by
    filter_upwards [hA', Body.ae_mem_cell c, hGreal] with p hq hmem hreal
    have hq' : (h : Chart → Merid) (cellPt c p) =
        Body.merReL ((G : Profile → MeridC) (Masked.cellPtInv c (cellPt c p))) := hq
    obtain ⟨-, ⟨h0, hcq⟩, -⟩ := hmem
    have hinv : Masked.cellPtInv c (cellPt c p) = p := Masked.cellPtInv_cellPt h0 hcq
    rw [hq', hinv, bct_merC_merReL_of_im hreal]
  -- the transport of `T0flat G`
  have hT := hR h G hGh
  have hT' : ∀ᵐ x ∂ageμ c (-3 / 2),
      (PartIIa.T0flat hc ν (μ : ℂ) G : Profile → MeridC) (Masked.cellPtInv c x) =
        NearInst.merC ((R0 h : Chart → Merid) x) := by
    have h1 : ∀ᵐ x ∂ageμ c (-3 / 2),
        (PartIIa.T0flat hc ν (μ : ℂ) G : Profile → MeridC) (Masked.cellPtInv c x) =
          NearInst.merC ((R0 h : Chart → Merid) (cellPt c (Masked.cellPtInv c x))) :=
      ct_ae_transfer hc (fun q => (PartIIa.T0flat hc ν (μ : ℂ) G : Profile → MeridC) q =
        NearInst.merC ((R0 h : Chart → Merid) (cellPt c q))) hT
    filter_upwards [h1, ct_cellPt_cellPtInv c hc] with x hx1 hx2
    rw [hx1, hx2]
  have hvel : ∀ᵐ x ∂ageμ c (-3 / 2), velC (R0 h : Chart → Merid) x =
      velF c (PartIIa.T0flat hc ν (μ : ℂ) G) x := by
    filter_upwards [hT'] with x hx
    funext i
    exact (congrArg (fun v : MeridC => v i) hx).symm
  -- the forcing hypothesis of `BodyColumnFlat`
  have hGx : ∀ᵐ x ∂ageμ c (-3 / 2), (G : Profile → MeridC) (Masked.cellPtInv c x) =
      ((Masked.cellPtInv c x).1 : ℂ) • divEps 0 M (Masked.cellPtInv c x) :=
    ct_ae_transfer hc (fun q => (G : Profile → MeridC) q = ((q.1 : ℂ) • divEps 0 M q)) hG
  have hGre : ∀ᵐ x ∂ageμ c (-3 / 2), ∀ i, ((G : Profile → MeridC) (Masked.cellPtInv c x) i).im = 0 :=
    ct_ae_transfer hc (fun q => ∀ i, ((G : Profile → MeridC) q i).im = 0) hGreal
  have hper : ∀ x : Chart, divEps 0 M (Masked.cellPtInv c x) = divEps 0 M x := fun x =>
    fsf_cellPtInv_periodic (c := c) (M := divEps 0 M) (bct_divEps_periodic hM) x
  have hfst : ∀ x : Chart, (Masked.cellPtInv c x).1 = x.1 := by
    rintro ⟨s, q, η⟩
    rfl
  have hVel : ∀ᵐ x ∂ageμ c (-3 / 2), ∀ i,
      velC (h : Chart → Merid) x i = (x.1 : ℂ) * divEps 0 M x i := by
    filter_upwards [hreA, hGx, hGre] with x hx1 hx2 hx3 i
    have hz : (((x.1 : ℂ) • divEps 0 M x) i).im = 0 := Masked.smul_divEps_im 0 M hMr x i
    rw [hper x, hfst x] at hx2
    show (((h : Chart → Merid) x i : ℝ) : ℂ) = _
    rw [hx1, hx2, bct_merReL_apply, bct_re_cast _ hz]
    rfl
  have hBh : ∀ᵐ x ∂ageμ c (-3 / 2), ∀ i,
      velC (h : Chart → Merid) x i = (x.1 : ℂ) * (fun x i => divEps 0 M x i) x i := hVel
  obtain ⟨b, Gr, hb, hcol⟩ :=
    hB c ν μ hc hν hμ R0 hR h (fun x i => divEps 0 M x i) hBh
  exact ⟨b, Gr, hb.trans hvel, hcol⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
