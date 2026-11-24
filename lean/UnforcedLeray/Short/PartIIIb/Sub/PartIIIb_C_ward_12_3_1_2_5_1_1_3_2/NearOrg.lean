import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2

/-!
# `InletENearJets`: organization (calculus for the ring lift near the axis)

Source `the November 2 reference manuscript`
lines 2545-2549 (on `ϱ < R` the inlet cutoff vanishes near the axis; arbitrary axial decay),
1206-1222.

Mathematics.  `E_i = realC (Nv R b_i τ)` with `b_i = p.inletProfile i` smooth, vanishing for
`s > H/2`, with jets of order `≤ 3` bounded by `M e^{-κ|η|}` (`InletProfileJets3`).  Since
`Nv R b τ y = 0` when `ϱ(y) < ρ₀ = R/√S` (`s = R²/ϱ² > S`; on the axis `age = 0`), the field vanishes
on an open neighbourhood of the axis, so only the shell `ρ₀ ≤ ϱ ≤ R₀` matters (`NvShellJets`),
where the chart `(s, ξ, η) = (R²/ϱ², ·, R y₃/ϱ)` has derivatives polynomial in `η`, absorbed by
`e^{-κ|η|}` with `|η| ≥ R|y₃|/R₀`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi UnforcedLeray.B0412

/-- **Leaf (source 2347-2369 + 2545-2549)**: the inlet profile `ringStreamProfile R (cutStream i)`
is smooth, vanishes for `s > H/2`, and its jets of order `≤ 3` decay like `M e^{-κ|η|}`
(`cutStreamJets` with `j = 4`, `ringStreamJetsDecay` with `j = 3`, `cutStreamSVanish`,
`ageCutoff_eq_zero`; exactly as `inletJetDecay_of` in `Short/PartII-b/Sub/PartII-b_G4_3_7_4.lean`
with `2` replaced by `3`; `κ := κ₀/(2c)`, `M` collects the `p`-dependent constants).  `ν₀ ≤ 1`
gives `1 ≤ c` and `1 ≤ R` as there. -/
def InletProfileJets3 : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ν₀ ≤ 1 ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.mode = q → ∀ i : Fin 2, ∃ M κ : ℝ, 0 ≤ M ∧ 0 < κ ∧
        ContDiff ℝ ∞ (p.inletProfile i) ∧
        (∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0) ∧
        ∀ l : ℕ, l ≤ 3 → ∀ x : ℝ × (ℝ × ℝ),
          ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤ M * Real.exp (-(κ * |x.2.2|))

/-- The conclusion of `InletENearJets` for the field `realC (Nv R b τ ·)` at one `(τ, y)` with
constant `C` and decay order `N`. -/
def NvJetsAt (R : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid) (N : ℕ) (C τ : ℝ) (y : UnforcedLeray.Space) :
    Prop :=
  (∀ k : ℕ, k ≤ 3 →
    ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => realC (Axi.Nv R b τ x)) y‖ ≤
      C * (1 + |y 2|) ^ (-(N : ℝ))) ∧
  (∀ k : ℕ, k ≤ 1 →
    ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
        UnforcedLeray.PhaseSpace.dτ (fun q : ℝ × UnforcedLeray.Space => realC (Axi.Nv R b q.1 q.2))
          (τ, x)) y‖ ≤ C * (1 + |y 2|) ^ (-(N : ℝ)))

/-- **Organize target (pure calculus; source 2545-2549, 1206-1222)**: shell jets of the ring lift.
For `R > 0`, `ρ₀ > 0`, a smooth meridional profile `b` with jets of order `≤ 3` bounded by
`M e^{-κ|η|}`, and any `N`, there is `C` with `NvJetsAt R b N C τ y` for all `τ ∈ ℝ` and all `y`
with `ρ₀ ≤ ϱ(y) ≤ R₀`.  (Chain rule through `y ↦ (R²/ϱ², Rτ/2-(R/2)log s, R y₃/ϱ)`, whose jets of
order `1..3` are `≤ C'(1+|y₃|)` on the shell; Faà di Bruno
`ContDiff.norm_iteratedFDeriv_comp_le`; frame `eR` and `√age = R/ϱ` smooth on the shell;
`∂_τ = (R/2)∂_ξ`; and `(1+|η|)^m e^{-κ|η|} ≤ C_N (1+|η|)^{-N}`, `|η| ≥ R|y₃|/R₀`.) -/
def NvShellJets : Prop :=
  ∀ (R ρ0 R0 κ M : ℝ), 0 < R → 0 < ρ0 → 0 < κ → 0 ≤ M →
    ∀ b : ℝ × (ℝ × ℝ) → Axi.Merid, ContDiff ℝ ∞ b →
      (∀ l : ℕ, l ≤ 3 → ∀ m : ℝ × (ℝ × ℝ),
        ‖iteratedFDeriv ℝ l b m‖ ≤ M * Real.exp (-(κ * |m.2.2|))) →
      ∀ N : ℕ, ∃ C : ℝ, ∀ τ : ℝ, ∀ y : UnforcedLeray.Space,
        ρ0 ≤ Axi.ϱ y → Axi.ϱ y ≤ R0 → NvJetsAt R b N C τ y

/-- Vanishing of the ring lift near the axis. -/
theorem Nv_eq_zero_of_lt {R S : ℝ} (hR : 0 < R) (hS : 0 < S) {b : ℝ × (ℝ × ℝ) → Axi.Merid}
    (hb : ∀ m : ℝ × (ℝ × ℝ), S < m.1 → b m = 0) (τ : ℝ) {y : UnforcedLeray.Space}
    (hy : Axi.ϱ y < R / Real.sqrt S) : Axi.Nv R b τ y = 0 := by
  by_cases h0 : Axi.ϱ y = 0
  · simp [Axi.Nv, Axi.age, h0]
  · have hpos : 0 < Axi.ϱ y := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
    have hsq : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
    have h1 : Axi.ϱ y * Real.sqrt S < R := by rwa [lt_div_iff₀ hsq] at hy
    have h2 : (Axi.ϱ y * Real.sqrt S) ^ 2 < R ^ 2 := by
      have := mul_self_lt_mul_self (by positivity) h1
      nlinarith
    have h3 : S < Axi.age R y := by
      unfold Axi.age
      rw [lt_div_iff₀ (by positivity)]
      have : (Axi.ϱ y * Real.sqrt S) ^ 2 = Axi.ϱ y ^ 2 * S := by
        rw [mul_pow, Real.sq_sqrt hS.le]
      nlinarith
    have : b (Axi.chart R τ y) = 0 := hb _ h3
    simp [Axi.Nv, this]

theorem nvNearJets_of_shell (h : NvShellJets) {R S κ M : ℝ} (hR : 0 < R) (hS : 0 < S) (hκ : 0 < κ)
    (hM : 0 ≤ M) {b : ℝ × (ℝ × ℝ) → Axi.Merid} (hbs : ContDiff ℝ ∞ b)
    (hb : ∀ m : ℝ × (ℝ × ℝ), S < m.1 → b m = 0)
    (hj : ∀ l : ℕ, l ≤ 3 → ∀ m : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l b m‖ ≤ M * Real.exp (-(κ * |m.2.2|))) (N : ℕ) (R0 : ℝ) :
    ∃ C : ℝ, ∀ τ : ℝ, ∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ R0 → NvJetsAt R b N C τ y := by
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
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [(hev.iteratedFDeriv ℝ k).self_of_nhds]
      have : iteratedFDeriv ℝ k (fun _ : UnforcedLeray.Space => (0 : UnforcedLeray.PhaseSpace.CVec3)) y = 0 := by
        simp
      rw [this]; simpa using hp
    · have hev2 : (fun x : UnforcedLeray.Space =>
          UnforcedLeray.PhaseSpace.dτ
            (fun q : ℝ × UnforcedLeray.Space => realC (Axi.Nv R b q.1 q.2)) (τ, x)) =ᶠ[nhds y]
          fun _ => (0 : UnforcedLeray.PhaseSpace.CVec3) := by
        filter_upwards [hopen.mem_nhds hshell |> fun h => (hopen.eventually_mem hshell)] with x hx
        have hnb : {q : ℝ × UnforcedLeray.Space | Axi.ϱ q.2 < R / Real.sqrt S} ∈ nhds (τ, x) := by
          refine (isOpen_lt (hcont.comp continuous_snd) continuous_const).mem_nhds hx
        have hq : (fun q : ℝ × UnforcedLeray.Space => realC (Axi.Nv R b q.1 q.2)) =ᶠ[nhds (τ, x)]
            fun _ => (0 : UnforcedLeray.PhaseSpace.CVec3) :=
          Filter.eventually_of_mem hnb (fun q hq => hz q.2 hq |>.trans rfl |> fun h => by
            simpa using (show realC (Axi.Nv R b q.1 q.2) = 0 from by
              rw [Nv_eq_zero_of_lt hR hS hb q.1 hq]; simp [realC]))
        simp [UnforcedLeray.PhaseSpace.dτ, hq.fderiv_eq]
      rw [(hev2.iteratedFDeriv ℝ k).self_of_nhds]
      have : iteratedFDeriv ℝ k (fun _ : UnforcedLeray.Space => (0 : UnforcedLeray.PhaseSpace.CVec3)) y = 0 := by
        simp
      rw [this]; simpa using hp

/-- `InletENearJets` from the two leaves. -/
theorem inletENearJets_of (h1 : InletProfileJets3) (h2 : NvShellJets) : InletENearJets := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, -, hν⟩ := h1 lam q hq dm dp hdm
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg hle hmode z g _ i N R0 hR0
  obtain ⟨M, κ, hM, hκ, hsm, hvan, hj⟩ := hν p d hreg hle hmode i
  have hH : 0 < p.H / 2 := half_pos p.H_pos
  obtain ⟨C, hC⟩ := nvNearJets_of_shell h2 p.R_pos hH hκ hM hsm hvan hj N R0
  refine ⟨C, fun τ _ y hy => hC τ y hy⟩

end UnforcedLeray.Short.PartIIIb.Concrete
