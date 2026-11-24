import UnforcedLeray.Short.PartIIIb.NearInst.Link.Clauses
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs

/-!
# The return-layer pins of the near link (source 1351-1362, 1556-1583, 1638-1679, 3888-3912,
4139-4146)

Source of record: `the November 2 reference manuscript` (73 pages).

`NearInst/Link/Agree.lean` states the link of a `Concrete.ReturnBase` with the near layer:
`IsNearLinked B o hν` (`B.M = o.MG`, `B.SN = o.SNG`) and `IsBodyLinked B Reps hν`
(`B.R = bodyG Reps`).  `Link/Clauses.lean` reduces `B.SN = o.SNG` to the function-level agreement
`Concrete.NearSNAgree B o` (task `C/near/link/3`).  This file derives the two remaining
identifications from the *physical* pins of `Concrete/PhysLayer.lean`:

* `NearSNAgreeAt` : `Concrete.IsStressInverse B ε μ` (`S = S_μ = R_μℙ div`, the Cartesian weak-stress
  inverse, 1556-1572, 4145), `Concrete.IsNearSplit B ε μ δ S` (`B.SN = B.S - S_far`, 3902-3912)
  and `IsMaskedNear p μ δ S o.SN` (`o.SN = S_ε - S_far'`, `S_ε` the real form of the stress map of
  `T_ε`, 1675-1679, 3888-3897) give `NearSNAgree B o`: "the finite-curvature free inverse is the
  conjugate of the Cartesian weak-stress inverse" (3888-3890), and the two far parts have the same
  exact kernel realization (3905-3912).
* `BodyLinkedAt` : `Concrete.IsBodyInverse B ε μ` (`R f` the free response of `𝒩_v f`, 1351-1362,
  4139-4146) and `IsBodyTransport Reps T_ε` (`T_ε = (μ - A_ε)⁻¹P_ε`, 1675-1677) give
  `IsBodyLinked B Reps hν`.

## Leaves (tasks)

* `TepsWeakSol` : the output of `T_ε` is a weak free solution: lifted by `𝒩_v` it is weakly
  solenoidal and solves `D_μ w = ℙ𝒩_v f` against solenoidal phase tests (1675-1677: `T_ε` is the
  chart conjugate of the Cartesian resolvent `R_μ = D_μ⁻¹` after the conjugated Cartesian Leray
  projection; 1351-1362).
* `ChartDivPair` : the exact chart divergence, `div(𝒩_T M) = 𝒩_v(s div_ε M)` for smooth band tensors,
  tested against phase tests (1660-1665, 3893-3897, "direct Cartesian differentiation").
* `StressMapWeakSol` : the real form `S_ε` of a stress map of `T_ε` gives, lifted, the Cartesian
  weak-stress solution `D_μ w = ℙ div 𝒩_T(F₁ + F₂)` (3888-3890; completion from smooth tensors,
  1678; 1556-1572).  Task: from `TepsWeakSol`, `ChartDivPair` and the density leaves of
  `Masked/Lemmas.lean`.
* `StressPairAE` : the stress pairing depends only on the a.e. class of the chart tensor (the chart
  `(τ, y) ↦ (s, q, η)` of 1640-1641 carries null sets to null sets).
* `FarMaskAgree` : two operators with the far pin (`Concrete.IsFarMaskG` on the gain-normed spaces,
  `IsFarMask` on `Z → H`) agree on stresses with the same component sum (3905-3912; identical
  kernel formula on box tensors, density `Masked.BoxDenseZ` and continuity).
* Reused: `Concrete.FreeWeakUniqueness` (1571, 1580-1583; task `IIIb-D2/1`, as the hypothesis
  `hU`), `Masked.CellPtH` (task `C/near/masked/2`).

## Assemblies (compiled here)

* `nearSNAgree_of` : `hU`, `StressPairAE`, `FarMaskAgree`, `StressMapWeakSol` give `NearSNAgreeAt`.
* `isBodyLinked_of` : `hU`, `Masked.CellPtH`, `TepsWeakSol` give `BodyLinkedAt`.
* `isNearLinked_of` : `MultLinkOf`, `NearLinkOf` (tasks `C/near/link/1`, `/3`) and `NearSNAgreeAt`
  give `IsNearLinked B o p.ν_pos` from `IsExactMultiplier B p.R V rb`, `IsActualNear p V rb μ δ S o`,
  `IsStressInverse` and `IsNearSplit`.

Note: the targets carry `P = 2εc ≤ 1` (needed by `free:weak-stress` uniqueness through
`bg:common-body-graph`, 1356) and `-1/4 < μ`; at the levels of use (`ν ≤ ν₀`, `μ ∈ K ⋐ (0,1/4)`)
both hold (`Masked.exists_period_le_one`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-! ## 1. Leaves -/

/-- **The stress pairing sees only the a.e. class of the chart tensor** (source 1640-1641,
2666-2668, 2683): the chart `(τ, y) ↦ (s, q, η)`, `s = R²/ρ²`, `q = R log(ρ/R) + Rτ/2`,
`η = Rz/ρ`, together with the azimuth, is a local diffeomorphism of `(ℝ/Pℤ) × (ℝ³ ∖ axis)` onto
`(0, ∞) × cell × ℝ × S¹`, so null sets of `s^{-1/2} ds dq dη` pull back to null sets of `dτ dy`,
and `T ↦ ⟨𝒩_T T, ∇Φ⟩` depends only on the a.e. class of `T`. -/
def StressPairAE : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ (g g' : Chart → Ten3), g =ᵐ[ageμ c (-1 / 2)] g' →
    ∀ Φ : ℝ × Space → CVec3,
      stressPair (2 * ε * c) (strPhys ε⁻¹ c g) Φ = stressPair (2 * ε * c) (strPhys ε⁻¹ c g') Φ

/-- **The two far parts agree on the same functions** (source 3902-3912): `S_far` is defined by its
exact kernel realization `1_{s<S} s^{-1/2}(-W_μ[1_{t>e^δ s}𝒩_T(T₁+T₂)])_{r,z}` on box tensors, the
same formula on the gain-normed spaces (`Concrete.IsFarMaskG`) and on `Z → H` (`IsFarMask`); box
inputs are dense (`Masked.BoxDenseZ`), both operators are continuous, and the kernel of the zero
tensor is zero.  Hence they agree on stresses with the same component sum `T₁ + T₂`. -/
def FarMaskAgree : Prop :=
  ∀ (c mZ ρb γ ν R μ δ Scut : ℝ), 0 < c → 0 ≤ mZ → 0 < ρb → 0 < ν →
    ∀ (Sf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν) (Sf' : Zsp c mZ ρb →L[ℝ] Hsp c),
      IsFarMaskG R μ δ Scut Sf → IsFarMask R ν μ δ Scut Sf' →
      ∀ (T : StrG c mZ ρb γ ν) (F : Zsp c mZ ρb), strSum T =ᵐ[ageμ c (-1 / 2)] zsum F →
        (Sf T : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] (Sf' F : Chart → Merid)

/-- **The output of `T_ε` is a weak free solution** (source 1675-1677 with 1351-1362, 4139-4146):
`T_ε = (μ - A_ε)⁻¹P_ε = B0223.RepsVec ∘ PartIIa.PepsC ε c` is the chart conjugate (lift
`B0223.liftVec`, `J_ε R_ε^vec(μ) = R(μ) J_ε`, `B0223.J_RepsVec`) of the Cartesian resolvent
`R(μ) = (μ + L)⁻¹`, `L = 𝒯 - νΔ - 1/2`, after the conjugated Cartesian Leray projection
(`B0226.Peps_eq_starProjection`).  So if the complexified recentred force `h'` has real chart form
`f` and `T_ε h'` has real chart form `w`, the lift `𝒩_v w` is weakly solenoidal and
`⟨D_μᵗΦ, 𝒩_v w⟩ = ⟨Φ, 𝒩_v f⟩` for every solenoidal phase test (on which `ℙ` is invisible). -/
def TepsWeakSol : Prop :=
  ∀ (p : Params) (μ : ℝ), p.period ≤ 1 → -(1 / 4) < μ → ∀ (γ : ℝ) (f : Chart → Merid)
    (h' : HSpace p.c MeridC) (w : VelG p.c γ p.ν),
    (h' : Profile → MeridC) =ᵐ[measureH p.c] (fun q => merC (f (cellPt p.c q))) →
    (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ) h' :
        Profile → MeridC) =ᵐ[measureH p.c] (fun q => merC ((w : Chart → Merid) (cellPt p.c q))) →
    IsWeakDmu p.ν μ (2 * p.ε * p.c) (velPhys p.ε⁻¹ p.c w)
      (fun Φ => pairF (2 * p.ε * p.c) Φ (velPhys p.ε⁻¹ p.c f))

/-- **The exact chart divergence** (source 1660-1665, 3893-3897, "direct Cartesian
differentiation"; lifts 2683): for a smooth, `c`-periodic, band-supported tensor `M` (the smooth
tensor tests `PartIIa.IsTensorTest` of the stress map, read through `tv4`), the Cartesian divergence
of `𝒩_T M = sM` is `𝒩_v(s div_ε M)`, `(div_ε M)_r = Q_εM_rr + ∂_ηM_rz - εM_φφ`,
`(div_ε M)_z = Q_εM_zr + ∂_ηM_zz`, `Q_ε = ∂_q - ε(2s∂_s + η∂_η + 1)`.  Against a phase test:
`⟨𝒩_v G, Φ⟩ = ⟨div 𝒩_T M, Φ⟩ = -⟨𝒩_T M, ∇Φ⟩` whenever `G` is (a.e.) the real chart field
`s div_ε M`. -/
def ChartDivPair : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ M : Chart → Ten3,
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)) → ∀ G : Chart → Merid,
    (∀ᵐ x ∂ageμ c (-3 / 2),
      merC (G x) = (x.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps ε (fun y => tv4 (M y)) x) →
    ∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c G) = -stressPair (2 * ε * c) (strPhys ε⁻¹ c M) Φ

/-- **The finite-curvature free inverse is the conjugate of the Cartesian weak-stress inverse**
(source 3888-3890; `S_ε = T_ε s div_ε` completed from smooth tensors, 1675-1679; `free:weak-stress`,
1556-1572): if `S_ε` is the real form (`IsStressTransport`) of a stress map of `T_ε`
(`PartIIa.IsStressMap`), then for every `F ∈ Z` the body velocity `w` with the chart function
`S_εF` is, lifted, a weakly solenoidal distributional solution of `D_μ w = ℙ div 𝒩_T(F₁ + F₂)`. -/
def StressMapWeakSol : Prop :=
  ∀ (p : Params) (μ : ℝ), p.period ≤ 1 → -(1 / 4) < μ → ∀ (mZ ρb γ : ℝ), 0 ≤ mZ → 0 < ρb →
    ∀ (Seps : Zsp p.c mZ ρb →L[ℝ] Hsp p.c)
      (Seps' : UnforcedLeray.Short.PartIIa.HTSpace p.c →L[ℂ] HSpace p.c MeridC),
      UnforcedLeray.Short.PartIIa.IsStressMap p.c p.ε
          (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ))
          Seps' →
      IsStressTransport Seps Seps' →
      ∀ (F : Zsp p.c mZ ρb) (w : VelG p.c γ p.ν),
        (w : Chart → Merid) =ᵐ[ageμ p.c (-3 / 2)] (Seps F : Chart → Merid) →
        IsWeakDmu p.ν μ (2 * p.ε * p.c) (velPhys p.ε⁻¹ p.c w)
          (fun Φ => -stressPair (2 * p.ε * p.c) (strPhys p.ε⁻¹ p.c (zsum F)) Φ)

/-! ## 2. Targets -/

/-- **The near inverse of the return layer is the near operator** (source 3888-3920, 4145, 5785) at a
level `p` with `P = 2εc ≤ 1`, real `μ > -1/4`, `m_Z ≥ 0`, `ρ_b > 0`: the physical pins
`S = S_μ`, `S_N = S_μ - S_far` and the near pin `S_N = S_ε - S_far` give `NearSNAgree`. -/
def NearSNAgreeAt : Prop :=
  ∀ (p : Params) (μ : ℝ), p.period ≤ 1 → -(1 / 4) < μ →
    ∀ (mZ ρb γ δ Scut : ℝ), 0 ≤ mZ → 0 < ρb →
    ∀ (Aff : Type) [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] [CompleteSpace Aff]
      (B : ReturnBase p.c mZ ρb γ p.ν Aff) (o : NearOps p.c mZ ρb),
      IsStressInverse B p.ε μ → IsNearSplit B p.ε μ δ Scut → IsMaskedNear p μ δ Scut o.SN →
      NearSNAgree B o

/-- **The body inverse of the return layer is the real form of `T_ε`** (source 1675-1677,
4084-4086, 4139-4146) at a level `p` with `P = 2εc ≤ 1` and real `μ > -1/4`. -/
def BodyLinkedAt : Prop :=
  ∀ (p : Params) (μ : ℝ), p.period ≤ 1 → -(1 / 4) < μ →
    ∀ (mZ ρb γ : ℝ) (Aff : Type) [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] [CompleteSpace Aff]
      (B : ReturnBase p.c mZ ρb γ p.ν Aff) (Reps : Hsp p.c →L[ℝ] Hsp p.c),
      IsBodyInverse B p.ε μ →
      IsBodyTransport Reps
        (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)) →
      IsBodyLinked B Reps p.ν_pos

/-! ## 3. Helpers -/

/-- Chart-a.e. statements pull back along the recentring `cellPt` (`Masked.CellPtH`). -/
theorem ae_cellPt_of {c : ℝ} (hH : Masked.CellPtH c) {P : Chart → Prop}
    (h : ∀ᵐ x ∂ageμ c (-3 / 2), P x) : ∀ᵐ q ∂measureH c, P (cellPt c q) := by
  have hle : Measure.map (cellPt c) (measureH c) ≤ ENNReal.ofReal c • ageμ c (-3 / 2) := hH.le
  have hac := Measure.absolutelyContinuous_of_le_smul hle
  exact ae_of_ae_map (Body.measurable_cellPt' c).aemeasurable (hac.ae_le h)

/-- The body velocity carrying the chart function of `u ∈ H`: `velIso⁻¹ (gainH⁻¹ (√π u))`. -/
def velOfH (c γ : ℝ) {ν : ℝ} (hν : 0 < ν) (u : Hsp c) : VelG c γ ν :=
  (velIso c γ ν).symm ((gainH c γ hν).symm (Real.sqrt Real.pi • u))

theorem coeFn_velOfH {c γ ν : ℝ} (hν : 0 < ν) (u : Hsp c) :
    (velOfH c γ hν u : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] (u : Chart → Merid) := by
  have h := coeFn_hOfVel (c := c) γ hν (velOfH c γ hν u)
  have e : gainH c γ hν (velIso c γ ν (velOfH c γ hν u)) = Real.sqrt Real.pi • u := by
    simp [velOfH]
  rw [e, smul_smul, inv_mul_cancel₀ sqrtPi_pos.ne', one_smul] at h
  exact h.symm

/-- `bodyG Reps f` carries the chart function of `R_ε h`, `h = (√π)⁻¹ srcIso f` the same force in
`H`. -/
theorem coeFn_bodyG {c γ ν : ℝ} (hν : 0 < ν) (Reps : Hsp c →L[ℝ] Hsp c) (f : SrcG c) :
    (bodyG Reps γ hν f : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      (Reps ((Real.sqrt Real.pi)⁻¹ • srcIso c f) : Chart → Merid) := by
  have h := coeFn_hOfVel (c := c) γ hν (bodyG Reps γ hν f)
  have e : gainH c γ hν (velIso c γ ν (bodyG Reps γ hν f)) = Reps (srcIso c f) := by
    simp [bodyG]
  rw [e, ← Reps.map_smul] at h
  exact h.symm

/-! ## 4. Assemblies -/

/-- **`NearSNAgree` from the physical pins** (source 3888-3912): `B.S T = w` with `w` the body
velocity of `S_εF` (`StressMapWeakSol`, `StressPairAE` and free weak uniqueness), and the far parts
agree (`FarMaskAgree`); subtract. -/
theorem nearSNAgree_of
    (hU : ∀ (c γ ν ε μ : ℝ), 0 < c → 0 < ν → 0 < ε → 2 * ε * c ≤ 1 → 0 < μ + 1 / 4 →
      FreeWeakUniqueness c γ ν ε μ)
    (h1 : StressPairAE) (h2 : FarMaskAgree) (h5 : StressMapWeakSol) : NearSNAgreeAt := by
  intro p μ hP hμ mZ ρb γ δ Scut hmZ hρ Aff _ _ _ B o hS hSplit hN T F hTF
  obtain ⟨Sf, hSf, hSN⟩ := hSplit
  obtain ⟨Seps, Sf', Seps', hmap, htr, hfar, hoSN⟩ := hN
  have hμ' : 0 < μ + 1 / 4 := by linarith
  set w : VelG p.c γ p.ν := velOfH p.c γ p.ν_pos (Seps F) with hwdef
  have hw : (w : Chart → Merid) =ᵐ[ageμ p.c (-3 / 2)] (Seps F : Chart → Merid) :=
    coeFn_velOfH p.ν_pos (Seps F)
  have hwsol := h5 p μ hP hμ mZ ρb γ hmZ hρ Seps Seps' hmap htr F w hw
  have hrhs : (fun Φ => -stressPair (2 * p.ε * p.c) (strPhys p.ε⁻¹ p.c (strSum T)) Φ) =
      (fun Φ => -stressPair (2 * p.ε * p.c) (strPhys p.ε⁻¹ p.c (zsum F)) Φ) := by
    funext Φ
    rw [h1 p.c p.ε p.c_pos p.ε_pos _ _ hTF Φ]
  have hST : IsWeakDmu p.ν μ (2 * p.ε * p.c) (velPhys p.ε⁻¹ p.c (B.S T))
      (fun Φ => -stressPair (2 * p.ε * p.c) (strPhys p.ε⁻¹ p.c (zsum F)) Φ) := by
    rw [← hrhs]
    exact hS T
  have hBS : B.S T = w := hU p.c γ p.ν p.ε μ p.c_pos p.ν_pos p.ε_pos hP hμ' _ _ _ hST hwsol
  have hfa := h2 p.c mZ ρb γ p.ν p.ε⁻¹ μ δ Scut p.c_pos hmZ hρ p.ν_pos Sf Sf' hSf hfar T F hTF
  have e1 : B.SN T = B.S T - Sf T := by rw [hSN]; rfl
  have e2 : o.SN F = Seps F - Sf' F := by rw [hoSN]; rfl
  have hsub1 := Lp.coeFn_sub (B.S T) (Sf T)
  rw [ae_bodyMeasure] at hsub1
  have hsub2 := Lp.coeFn_sub (Seps F) (Sf' F)
  rw [e1, e2]
  filter_upwards [hsub1, hsub2, hw, hfa] with x a1 a2 a3 a4
  rw [a1, a2, Pi.sub_apply, Pi.sub_apply, hBS, a3, a4]

/-- **`IsBodyLinked` from the physical body pin** (source 1351-1362, 1675-1677, 4139-4146): the body
velocity `bodyG Reps f` carries `R_ε h`, `h` the same force in `H`; its lift is a weak free
solution (`TepsWeakSol`), as is that of `B.R f` (`IsBodyInverse`); free weak uniqueness. -/
theorem isBodyLinked_of
    (hU : ∀ (c γ ν ε μ : ℝ), 0 < c → 0 < ν → 0 < ε → 2 * ε * c ≤ 1 → 0 < μ + 1 / 4 →
      FreeWeakUniqueness c γ ν ε μ)
    (hH : ∀ c : ℝ, 0 < c → Masked.CellPtH c) (h3 : TepsWeakSol) : BodyLinkedAt := by
  intro p μ hP hμ mZ ρb γ Aff _ _ _ B Reps hR hT
  have hμ' : 0 < μ + 1 / 4 := by linarith
  have hHc := hH p.c p.c_pos
  show B.R = bodyG Reps γ p.ν_pos
  ext1 f
  set h : Hsp p.c := (Real.sqrt Real.pi)⁻¹ • srcIso p.c f with hhdef
  have hh : (h : Chart → Merid) =ᵐ[ageμ p.c (-3 / 2)] (f : Chart → Merid) := coeFn_hOfSrc f
  -- the complexified recentred force
  have hh0 := Body.cplxH_ae p.c hHc h
  have hpull := ae_cellPt_of hHc hh
  have hh' : (Body.cplxH p.c hHc h : Profile → MeridC) =ᵐ[measureH p.c]
      (fun q => merC ((f : Chart → Merid) (cellPt p.c q))) := by
    filter_upwards [hh0, hpull] with q a1 a2
    rw [a1, a2]
  -- the body velocity of `R_ε h`
  set w : VelG p.c γ p.ν := bodyG Reps γ p.ν_pos f with hwdef
  have hwR := coeFn_bodyG (γ := γ) p.ν_pos Reps f
  have hwpull := ae_cellPt_of hHc hwR
  have hTw : (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl
      (μ : ℂ) (Body.cplxH p.c hHc h) : Profile → MeridC) =ᵐ[measureH p.c]
      (fun q => merC ((w : Chart → Merid) (cellPt p.c q))) := by
    filter_upwards [hT h (Body.cplxH p.c hHc h) hh0, hwpull] with q a1 a2
    rw [a1, a2]
  have hwsol := h3 p μ hP hμ γ f (Body.cplxH p.c hHc h) w hh' hTw
  have hRf : IsWeakDmu p.ν μ (2 * p.ε * p.c) (velPhys p.ε⁻¹ p.c (B.R f))
      (fun Φ => pairF (2 * p.ε * p.c) Φ (velPhys p.ε⁻¹ p.c f)) :=
    ⟨(hR f).solenoidal, (hR f).equation⟩
  exact hU p.c γ p.ν p.ε μ p.c_pos p.ν_pos p.ε_pos hP hμ' _ _ _ hRf hwsol

/-- **The near link from the physical pins** (source 3876-3878, 3888-3920, 5779-5787): the exact
multiplier pin and the stress/near-split pins of the return base, with the actual near operators,
give `IsNearLinked` (packaging of `MultLinkOf`, `NearLinkOf` and `NearSNAgreeAt`). -/
theorem isNearLinked_of (hML : MultLinkOf) (hNL : NearLinkOf) (hNS : NearSNAgreeAt)
    {p : Params} {μ : ℝ} (hP : p.period ≤ 1) (hμ : -(1 / 4) < μ) {mZ ρb γ δ Scut : ℝ}
    (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] {B : ReturnBase p.c mZ ρb γ p.ν Aff} {o : NearOps p.c mZ ρb}
    {V rb : ℝ → UnforcedLeray.SpatialField}
    (hM : IsExactMultiplier B p.R V rb) (hA : IsActualNear p V rb μ δ Scut o)
    (hS : IsStressInverse B p.ε μ) (hSp : IsNearSplit B p.ε μ δ Scut) :
    IsNearLinked B o p.ν_pos :=
  ⟨hML p.c mZ ρb γ p.ν p.ν_pos Aff B o p.R V rb hM hA.split,
    hNL p.c mZ ρb γ p.ν p.ν_pos hρ Aff B o
      (hNS p μ hP hμ mZ ρb γ δ Scut hmZ hρ Aff B o hS hSp hA.near)⟩

end UnforcedLeray.Short.PartIIIb.NearInst
