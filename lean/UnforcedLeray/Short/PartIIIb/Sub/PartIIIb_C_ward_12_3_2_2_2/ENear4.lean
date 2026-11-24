import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.InletProfileJets3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Shell.Main

/-!
# `inletENearJets4 : InletENearJets4`

Source `the November 2 reference manuscript`
lines 2545-2551, 2385-2387, 1206-1222.  Order-4 analogue of `inletENearJets`
(`Sub/PartIII-b_C_ward_12_3_1_2_5_1_1_3_2/Jets.lean`): on the disc `ϱ ≤ R₀`, spatial derivatives of
order `≤ 4` of `E_i = realC (Nv R (inletProfile i) τ)` and spatial derivatives of order `≤ 2` of
`∂_τ E_i` are bounded by `C (1 + |y₃|)^{-N}`, uniformly in `τ ∈ (0, P]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi UnforcedLeray.B0412

/-- Order-4 analogue of `InletProfileJets3` (source 2347-2369, 2545-2551): jets of order `≤ 4` of
`p.inletProfile i` decay like `M e^{-κ|η|}`. -/
def InletProfileJets4 : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ν₀ ≤ 1 ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.mode = q → ∀ i : Fin 2, ∃ M κ : ℝ, 0 ≤ M ∧ 0 < κ ∧
        ContDiff ℝ ∞ (p.inletProfile i) ∧
        (∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0) ∧
        ∀ l : ℕ, l ≤ 4 → ∀ x : ℝ × (ℝ × ℝ),
          ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤ M * Real.exp (-(κ * |x.2.2|))

theorem inletProfileJets4 : InletProfileJets4 := by
  intro lam q hq dm dp hdm
  obtain ⟨C3, κ0, N, hC3, hκ0, h3'⟩ := UnforcedLeray.Short.IIb.cutStreamJets lam q hq 5
  obtain ⟨C4, hC4, h4'⟩ := UnforcedLeray.Short.IIb.ringStreamJetsDecay 4
  refine ⟨1, one_pos, le_refl _, ?_⟩
  intro p d hreg hν hmode i
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hcpos : 0 < p.c := by linarith
  have hR1 : 1 ≤ p.R := by
    have hε : p.ε ≤ 1 := by
      rw [hreg.eps_eq]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ d / p.ν := div_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hνpos.le
      rw [neg_div]; linarith
    show 1 ≤ p.ε⁻¹
    exact one_le_inv₀ p.ε_pos |>.mpr hε
  have hH : 0 < p.H := p.H_pos
  have hHi : 0 ≤ p.H⁻¹ := inv_nonneg.2 hH.le
  obtain ⟨hcutsm, hcut⟩ := h3' p hmode hc1 hH i
  have hM0 : 0 ≤ C3 * (1 + p.H⁻¹) ^ 5 * p.c ^ N :=
    mul_nonneg (mul_nonneg hC3.le (pow_nonneg (by linarith) 5)) (pow_nonneg hcpos.le N)
  have hring := h4' p.R (p.H / 2) p.c κ0 (C3 * (1 + p.H⁻¹) ^ 5 * p.c ^ N) (p.cutStream i)
    hR1 (half_pos hH) hcpos hκ0 hM0
    hcutsm
    (by
      intro x hx
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH (show p.H / 2 ≤ x.1 from hx.le)])
    (fun x hx => UnforcedLeray.Short.IIb.cutStreamSVanish lam q hq p hmode hc1 hH i x hx)
    (fun l hl x => hcut l hl x)
  have hκpos : 0 < κ0 / (2 * p.c) := div_pos hκ0 (by linarith)
  refine ⟨C4 * (1 + p.H / 2) * (1 + p.c / κ0) * (C3 * (1 + p.H⁻¹) ^ 5 * p.c ^ N),
    κ0 / (2 * p.c), ?_, hκpos, ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg hC4.le (by linarith))
      (by have := div_nonneg hcpos.le hκ0.le; linarith)) hM0
  · unfold Params.inletProfile
    exact UnforcedLeray.Short.IIb.inletCD_ringStreamProfile hcutsm
  · intro x hx
    have hcut0 : p.cutStream i x = 0 := by
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH hx.le]
    have hev : ∀ᶠ y in 𝓝 x, p.H / 2 < y.1 :=
      (continuous_fst.tendsto x).eventually (lt_mem_nhds hx)
    have hfun : p.cutStream i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with y hy
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH hy.le]
    have hfd : fderiv ℝ (p.cutStream i) x = 0 := by
      rw [hfun.fderiv_eq]
      simp
    have hdS : Axi.dS (p.cutStream i) x = 0 := by
      unfold Axi.dS
      rw [hfd]
      simp
    have hdQ : Axi.dQ (p.cutStream i) x = 0 := by
      unfold Axi.dQ
      rw [hfd]
      simp
    have hdE : Axi.dEta (p.cutStream i) x = 0 := by
      unfold Axi.dEta
      rw [hfd]
      simp
    simp [Params.inletProfile, Axi.ringStreamProfile, hdS, hdQ, hdE, hcut0]
  · intro l hl x
    have hmain := hring l (by omega) x
    rw [show -((κ0 / 2) * |x.2.2| / p.c) = -((κ0 / (2 * p.c)) * |x.2.2|) by ring] at hmain
    exact hmain

/-- The conclusion of `InletENearJets4` for the field `realC (Nv R b τ ·)` at one `(τ, y)` with
constant `C` and decay order `N`. -/
def NvJetsAt4 (R : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid) (N : ℕ) (C τ : ℝ) (y : UnforcedLeray.Space) :
    Prop :=
  (∀ k : ℕ, k ≤ 4 →
    ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => realC (Axi.Nv R b τ x)) y‖ ≤
      C * (1 + |y 2|) ^ (-(N : ℝ))) ∧
  (∀ k : ℕ, k ≤ 2 →
    ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
        UnforcedLeray.PhaseSpace.dτ (fun q : ℝ × UnforcedLeray.Space => realC (Axi.Nv R b q.1 q.2))
          (τ, x)) y‖ ≤ C * (1 + |y 2|) ^ (-(N : ℝ)))

/-- Order-4 shell jets of the ring lift (`k ≤ 4` for `E` and `k ≤ 2` for `∂_τ E`). -/
def NvShellJets4 : Prop :=
  ∀ (R ρ0 R0 κ M : ℝ), 0 < R → 0 < ρ0 → 0 < κ → 0 ≤ M →
    ∀ b : ℝ × (ℝ × ℝ) → Axi.Merid, ContDiff ℝ ∞ b →
      (∀ l : ℕ, l ≤ 4 → ∀ m : ℝ × (ℝ × ℝ),
        ‖iteratedFDeriv ℝ l b m‖ ≤ M * Real.exp (-(κ * |m.2.2|))) →
      ∀ N : ℕ, ∃ C : ℝ, ∀ τ : ℝ, ∀ y : UnforcedLeray.Space,
        ρ0 ≤ Axi.ϱ y → Axi.ϱ y ≤ R0 → NvJetsAt4 R b N C τ y

theorem nvShellJets4_of (hF : Shell.ShellFrameJets) (hA : Shell.ShellAgeJets)
    (hP : Shell.ShellPhaseJets) (hT : Shell.ShellTransJets) (hX : Shell.ShellAbsorb)
    (hD : Shell.ShellDτ) : NvShellJets4 := by
  intro R ρ0 R0 κ M hR hρ0 hκ hM b hb hj N
  obtain ⟨C1, hC1⟩ := Shell.shellLiftJets_of hF hA hP hT hX hR hρ0 hκ hM 4 hb hj N
  have hb's : ContDiff ℝ ∞ (fun m => (R / 2) • dQ b m) :=
    (Shell.contDiff_dQ hb).const_smul (R / 2)
  have hj' : ∀ l : ℕ, l ≤ 2 → ∀ m : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l (fun m => (R / 2) • dQ b m) m‖ ≤
        (R / 2 * M) * Real.exp (-(κ * |m.2.2|)) := by
    intro l hl m
    have h1 : iteratedFDeriv ℝ l (fun m => (R / 2) • dQ b m) m =
        (R / 2) • iteratedFDeriv ℝ l (dQ b) m :=
      iteratedFDeriv_const_smul_apply'
        ((Shell.contDiff_dQ hb).contDiffAt.of_le (by exact_mod_cast le_top))
    rw [h1, norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((Shell.norm_iteratedFDeriv_dQ_le hb l m).trans (hj (l + 1) (by omega) m)) (by positivity)
  obtain ⟨C2, hC2⟩ := Shell.shellLiftJets_of hF hA hP hT hX hR hρ0 hκ (by positivity) 2 hb's hj' N
  refine ⟨max C1 C2, fun τ y hy1 hy2 => ⟨fun k hk => ?_, fun k hk => ?_⟩⟩
  · have hp : 0 ≤ (1 + |y 2|) ^ (-(N : ℝ)) := by positivity
    exact (hC1 τ y hy1 hy2 k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  · have hp : 0 ≤ (1 + |y 2|) ^ (-(N : ℝ)) := by positivity
    have hax := Shell.notMem_axis_of_le hρ0 hy1
    have hev : (fun x : UnforcedLeray.Space => UnforcedLeray.PhaseSpace.dτ
          (fun q : ℝ × UnforcedLeray.Space => UnforcedLeray.B0412.realC (Nv R b q.1 q.2))
            (τ, x)) =ᶠ[nhds y]
        (fun x => UnforcedLeray.B0412.realC (Nv R (fun m => (R / 2) • dQ b m) τ x)) := by
      filter_upwards [isOpen_compl_axis.mem_nhds hax] with x hx
      exact hD R b hR hb τ x hx
    rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
    exact (hC2 τ y hy1 hy2 k hk).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)

theorem nvShellJets4 : NvShellJets4 :=
  nvShellJets4_of Shell.shellFrameJets Shell.shellAgeJets Shell.shellPhaseJets
    Shell.shellTransJets Shell.shellAbsorb Shell.shellDτ

theorem nvNearJets4_of_shell (h : NvShellJets4) {R S κ M : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hκ : 0 < κ) (hM : 0 ≤ M) {b : ℝ × (ℝ × ℝ) → Axi.Merid} (hbs : ContDiff ℝ ∞ b)
    (hb : ∀ m : ℝ × (ℝ × ℝ), S < m.1 → b m = 0)
    (hj : ∀ l : ℕ, l ≤ 4 → ∀ m : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l b m‖ ≤ M * Real.exp (-(κ * |m.2.2|))) (N : ℕ) (R0 : ℝ) :
    ∃ C : ℝ, ∀ τ : ℝ, ∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ R0 → NvJetsAt4 R b N C τ y := by
  have hsq : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have hρ : 0 < R / Real.sqrt S := div_pos hR hsq
  obtain ⟨C, hC⟩ := h R (R / Real.sqrt S) R0 κ M hR hρ hκ hM b hbs hj N
  refine ⟨max C 0, fun τ y hy => ?_⟩
  by_cases hshell : R / Real.sqrt S ≤ Axi.ϱ y
  · obtain ⟨h1, h2⟩ := hC τ y hshell hy
    have hp : 0 < (1 + |y 2|) ^ (-(N : ℝ)) := by positivity
    exact ⟨fun k hk => (h1 k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le),
      fun k hk => (h2 k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)⟩
  · push_neg at hshell
    have hp : 0 ≤ max C 0 * (1 + |y 2|) ^ (-(N : ℝ)) := by positivity
    have hcont : Continuous (fun x : UnforcedLeray.Space => Axi.ϱ x) := by
      unfold Axi.ϱ; fun_prop
    have hopen : IsOpen {x : UnforcedLeray.Space | Axi.ϱ x < R / Real.sqrt S} :=
      isOpen_lt hcont continuous_const
    have hnhds : {x : UnforcedLeray.Space | Axi.ϱ x < R / Real.sqrt S} ∈ nhds y :=
      hopen.mem_nhds hshell
    have hz : ∀ x ∈ {x : UnforcedLeray.Space | Axi.ϱ x < R / Real.sqrt S},
        realC (Axi.Nv R b τ x) = 0 := fun x hx => by
      rw [Nv_eq_zero_of_lt hR hS hb τ hx]; simp [realC]
    have hev : (fun x : UnforcedLeray.Space => realC (Axi.Nv R b τ x)) =ᶠ[nhds y]
        fun _ => (0 : UnforcedLeray.PhaseSpace.CVec3) :=
      Filter.eventually_of_mem hnhds hz
    refine ⟨fun k _ => ?_, fun k _ => ?_⟩
    · rw [(hev.iteratedFDeriv ℝ k).self_of_nhds]
      have : iteratedFDeriv ℝ k (fun _ : UnforcedLeray.Space => (0 : UnforcedLeray.PhaseSpace.CVec3)) y = 0 := by
        simp
      rw [this]; simpa using hp
    · have hev2 : (fun x : UnforcedLeray.Space =>
          UnforcedLeray.PhaseSpace.dτ
            (fun q : ℝ × UnforcedLeray.Space => realC (Axi.Nv R b q.1 q.2)) (τ, x)) =ᶠ[nhds y]
          fun _ => (0 : UnforcedLeray.PhaseSpace.CVec3) := by
        filter_upwards [hopen.mem_nhds hshell |> fun _ => (hopen.eventually_mem hshell)] with x hx
        have hnb : {q : ℝ × UnforcedLeray.Space | Axi.ϱ q.2 < R / Real.sqrt S} ∈ nhds (τ, x) := by
          refine (isOpen_lt (hcont.comp continuous_snd) continuous_const).mem_nhds hx
        have hq : (fun q : ℝ × UnforcedLeray.Space => realC (Axi.Nv R b q.1 q.2)) =ᶠ[nhds (τ, x)]
            fun _ => (0 : UnforcedLeray.PhaseSpace.CVec3) :=
          Filter.eventually_of_mem hnb (fun q hq => hz q.2 hq |>.trans rfl |> fun _ => by
            simpa using (show realC (Axi.Nv R b q.1 q.2) = 0 from by
              rw [Nv_eq_zero_of_lt hR hS hb q.1 hq]; simp [realC]))
        simp [UnforcedLeray.PhaseSpace.dτ, hq.fderiv_eq]
      rw [(hev2.iteratedFDeriv ℝ k).self_of_nhds]
      have : iteratedFDeriv ℝ k (fun _ : UnforcedLeray.Space => (0 : UnforcedLeray.PhaseSpace.CVec3)) y = 0 := by
        simp
      rw [this]; simpa using hp

theorem inletENearJets4_of (h1 : InletProfileJets4) (h2 : NvShellJets4) : InletENearJets4 := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, -, hν⟩ := h1 lam q hq dm dp hdm
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg hle hmode z g _ i N R0 _
  obtain ⟨M, κ, hM, hκ, hsm, hvan, hj⟩ := hν p d hreg hle hmode i
  have hH : 0 < p.H / 2 := half_pos p.H_pos
  obtain ⟨C, hC⟩ := nvNearJets4_of_shell h2 p.R_pos hH hκ hM hsm hvan hj N R0
  refine ⟨C, fun τ _ y hy => hC τ y hy⟩

/-- **`InletENearJets4`** (source 2545-2551, 2385-2387, 1206-1222). -/
theorem inletENearJets4 : InletENearJets4 :=
  inletENearJets4_of inletProfileJets4 nvShellJets4

end UnforcedLeray.Short.PartIIIb.Concrete
