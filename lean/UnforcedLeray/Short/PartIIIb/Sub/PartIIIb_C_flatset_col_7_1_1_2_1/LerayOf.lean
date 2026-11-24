import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs

/-!
# `LerayDriving` from its leaves (conditional assembly)

Source `the November 2 reference manuscript` 1650-1656, 1676-1677 (see
`LerayDefs.lean` for the route).  Proved here:

* `pepsC_eq_of_decomp`: `P₀ (a + b) = a` for `a ∈ solenoidalHC 0 c`, `b ∈ (solenoidalHC 0 c)ᗮ`
  (`P₀ = PepsC 0 c` is the orthogonal projection, `PartII-a/StatementsNear.lean:112`);
* `cylKerGreen_of`: the cylinder fundamental solution from its regularisation;
* `lerayDriving_of`: `LerayDriving` with `G = lerayField c F / s`, `F` the force field of
  `IsSmoothForce`;
* small facts on `lerayPot` (periodicity, `s`-band) and `flatGrad`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-! ## Elementary facts -/

/-- `lerayPot c F` is `c`-periodic in `q` when `F` is. -/
theorem lerayPot_periodic {c : ℝ} {F : Chart → Fin 2 → ℝ}
    (hF : ∀ s q η, F (s, (q + c, η)) = F (s, (q, η))) (s q η : ℝ) :
    lerayPot c F (s, (q + c, η)) = lerayPot c F (s, (q, η)) := by
  have key : ∀ y : ℝ × ℝ, F (s, (q + c, η) - y) = F (s, (q, η) - y) := by
    intro y
    have h := hF s (q - y.1) (η - y.2)
    have e1 : (q + c, η) - y = (q - y.1 + c, η - y.2) := by
      ext <;> simp; ring
    have e2 : (q, η) - y = (q - y.1, η - y.2) := by
      ext <;> simp
    rw [e1, e2, h]
  unfold lerayPot
  simp only [key]

/-- `lerayPot c F` vanishes outside the `s`-band of `F`. -/
theorem lerayPot_band {c : ℝ} {F : Chart → Fin 2 → ℝ} {s0 s1 : ℝ}
    (hF : ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1) (p : Chart) (hp : lerayPot c F p ≠ 0) :
    p.1 ∈ Icc s0 s1 := by
  by_contra hs
  apply hp
  unfold lerayPot
  refine Finset.sum_eq_zero fun i _ => ?_
  have h0 : ∀ y : ℝ × ℝ, F (p.1, p.2 - y) = 0 := fun y => by
    by_contra hne
    exact hs (hF (p.1, p.2 - y) hne)
  simp [h0]

/-- A `c`-periodic chart function is invariant under the recentring `cellPt`. -/
theorem eq_cellPt {X : Type*} {c : ℝ} {f : Chart → X}
    (hf : ∀ s q η, f (s, (q + c, η)) = f (s, (q, η))) (p : Chart) :
    f (NearInst.cellPt c p) = f p := by
  obtain ⟨s, q, η⟩ := p
  show f (s, (if q < c / 2 then q else q - c, η)) = f (s, (q, η))
  split_ifs
  · rfl
  · have h := hf s (q - c) η
    rw [sub_add_cancel] at h
    exact h.symm

/-- A function vanishing outside an `s`-band has zero derivative outside it. -/
theorem fderiv_eq_zero_of_band {u : Chart → ℝ} {s0 s1 : ℝ}
    (hu : ∀ p, u p ≠ 0 → p.1 ∈ Icc s0 s1) {p : Chart} (hp : p.1 ∉ Icc s0 s1) :
    fderiv ℝ u p = 0 := by
  have hopen : IsOpen {x : Chart | x.1 ∉ Icc s0 s1} :=
    (isClosed_Icc.preimage continuous_fst).isOpen_compl
  have hev : u =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hp] with x hx
    by_contra hne
    exact hx (hu x hne)
  rw [hev.fderiv_eq]
  simp

theorem flatGrad_band {u : Chart → ℝ} {s0 s1 : ℝ} (hu : ∀ p, u p ≠ 0 → p.1 ∈ Icc s0 s1)
    (p : Chart) (hp : flatGrad u p ≠ 0) : p.1 ∈ Icc s0 s1 := by
  by_contra hs
  apply hp
  have h0 := fderiv_eq_zero_of_band hu hs
  funext i
  fin_cases i <;> simp [flatGrad, UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dEta, h0]

theorem flatGrad_continuous {u : Chart → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 2) :
    Continuous fun p => flatGrad u p i := by
  have hd : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have h0 : Continuous fun p => fderiv ℝ u p ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) :=
    hd.clm_apply continuous_const
  have h1 : Continuous fun p => fderiv ℝ u p ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) :=
    hd.clm_apply continuous_const
  fin_cases i
  · simpa [flatGrad, UnforcedLeray.Axi.dQ] using h0
  · simpa [flatGrad, UnforcedLeray.Axi.dEta] using h1

theorem flatGrad_decay {u : Chart → ℝ} {C κ : ℝ}
    (h : ∀ p : Chart, |UnforcedLeray.Axi.dQ u p| + |UnforcedLeray.Axi.dEta u p| ≤
      C * Real.exp (-(κ * |p.2.2|)))
    (p : Chart) (i : Fin 2) : |flatGrad u p i| ≤ C * Real.exp (-(κ * |p.2.2|)) := by
  have h1 := h p
  have a1 := abs_nonneg (UnforcedLeray.Axi.dQ u p)
  have a2 := abs_nonneg (UnforcedLeray.Axi.dEta u p)
  fin_cases i
  · simp only [flatGrad]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    linarith
  · simp only [flatGrad]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linarith

/-! ## The projection -/

/-- `P₀ (a + b) = a` for `a` solenoidal and `b` orthogonal to the solenoidal space. -/
theorem pepsC_eq_of_decomp {c : ℝ} {a b : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC}
    (ha : a ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c)
    (hb : b ∈ (UnforcedLeray.Short.PartIIa.solenoidalHC 0 c)ᗮ) :
    UnforcedLeray.Short.PartIIa.PepsC 0 c (a + b) = a := by
  unfold UnforcedLeray.Short.PartIIa.PepsC
  rw [map_add, Submodule.starProjection_eq_self_iff.2 ha,
    (Submodule.starProjection_apply_eq_zero_iff _).2 hb, add_zero]

/-! ## The cylinder fundamental solution -/

theorem cylKerGreen_of (h1 : RegKerIBP) (h2 : RegApproxId) (h3 : RegKerLimit) : CylKerGreen := by
  intro c hc h hh i
  have hlim1 := h3 c hc h hh i
  have hlim2 : Tendsto (fun ε => ∫ y in cellC c, cylKerReg c ε i y * lap2 h y) (𝓝[>] 0)
      (𝓝 (-pd2 i h 0)) := by
    refine (h2 c hc h hh i).neg.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (h1 c ε hc hε h hh i).symm
  exact tendsto_nhds_unique hlim1 hlim2

/-! ## Assembly -/

/-- **`LerayDriving` from its leaves**: `G = (F - ∇u)/s`, `u = lerayPot c F`. -/
theorem lerayDriving_of (hD : DrivingOfSmooth) (hS : SmoothSolenoidal) (hP : SmoothGradPerp)
    (hM : MemLpOfDecay) (hR : SmoothForceRep) (hW : LerayFieldProps) (hU : LerayPotSmooth)
    (hUd : LerayPotDecay) : LerayDriving := by
  intro c hc g hg
  obtain ⟨F, hFs, hFp, hFb, hae⟩ := hg
  have hF : IsForceField c F := ⟨hFs, hFp, hFb⟩
  obtain ⟨hWs, hWp, hWb, hWd, hWe, hWdiv⟩ := hW c hc F hF
  refine ⟨fun p i => lerayField c F p i / p.1, hD c _ hWs hWp hWb hWd, ?_⟩
  intro f' hf'
  obtain ⟨hus, hub, -⟩ := hU c hc F hF
  obtain ⟨Cd, κd, hκd, hdec⟩ := hUd c hc F hF
  obtain ⟨s0, s1, L, hs0, hFb'⟩ := hFb
  have huband : ∀ p, lerayPot c F p ≠ 0 → p.1 ∈ Icc s0 s1 :=
    lerayPot_band (fun p hp => (hFb' p hp).1)
  have hubdd : ∃ C : ℝ, ∀ p, |lerayPot c F p| ≤ C := by
    obtain ⟨C, hC⟩ := hub 0
    refine ⟨C, fun p => ?_⟩
    have := hC p
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hWm := hM c hc (lerayField c F) (fun i => (hWs i).continuous) hWb hWe
  have hVm := hM c hc (flatGrad (lerayPot c F)) (flatGrad_continuous hus)
    ⟨s0, s1, hs0, flatGrad_band huband⟩ ⟨Cd, κd, hκd, flatGrad_decay hdec⟩
  have ha := hS c hc (lerayField c F) hWs hWp hWdiv hWm
  have hb := hP c hc (lerayPot c F) hus (lerayPot_periodic hFp) ⟨s0, s1, hs0, huband⟩ hubdd
    ⟨Cd, κd, hκd, hdec⟩ hVm
  have hrep := hR c hc g F hFp hae
  have hsum : f' = hWm.toLp _ + hVm.toLp _ := by
    apply Lp.ext
    filter_upwards [hf', hrep, hWm.coeFn_toLp, hVm.coeFn_toLp,
      Lp.coeFn_add (hWm.toLp _) (hVm.toLp _)] with p h1 h2 h3 h4 h5
    rw [h5, Pi.add_apply, h3, h4, h1, h2]
    ext i
    simp only [cvec, lerayField, PiLp.add_apply]
    push_cast
    ring
  rw [hsum, pepsC_eq_of_decomp ha hb]
  filter_upwards [hWm.coeFn_toLp, UnforcedLeray.B0220.ae_cell_measureH c] with p h1 hcell
  rw [h1]
  have hp1 : 0 < p.1 := hcell.1
  have hper : lerayField c F (NearInst.cellPt c p) = lerayField c F p := eq_cellPt hWp p
  have hfst : (NearInst.cellPt c p).1 = p.1 := rfl
  ext i
  simp only [cvec, hper, hfst]
  rw [mul_div_cancel₀ _ hp1.ne']

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
