import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.TableOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.ShiftedResolvent
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.Props

/-!
# `PartIII-b:C/rep/4/2/org/3/4`: the multiplier step of the thin transition table

Source `the November 2 reference manuscript` 5312-5316 (both transitions, support
`0.8/ν < s < 1/ν`), 5317-5318 (late output), 5323-5340 (the thin-source row of the table: thin
receiver `ε²`, scaled repair receiver `ε^{49/22}e^{m₀/(2ν)}`, `ρ = ε^{3/11}e^{m₀/ν}`; "The outward
stream primitive has the same norm powers"), 5342-5352 (thin-to-thin: "The separated pointwise
velocity is at most `P_νε²s²N_0`", then the normalized velocity lift and thin multiplication),
3669-3679 (`sep:thin-global`: a thin source with `∫‖T(z,·)‖_{L²_τ}dz ≤ R²N₀`, "the same argument
with `p = 1`"), 3683-3701 (the stream cutoff: "`(4.x)`–`sep:thin-global` remain valid after this
cutoff"), 3729-3730 (physical mass `R²N₀`), 5573-5592.

`TransMultiplierStepAt` (`TableOrg.lean`) is proved here (`transMultiplierStep_of`, with the
`S`-degree `k₁ = 0`: the transitions live on the bounded window `s ≤ 1/ν`) by the chain of the
repair-source table (`YRepStream/TransTable`), with the mass `N₀` in place of the
`L²_τL^{22/19}` source norm:

1. **The separated source.**  The chart tensor of the old thin source is `oldThinTen T = χ̂_o(νs)T₁`
   (`Annulus/Defs.lean`); it vanishes for `νs ≤ 6/5`, so its lift `S = 𝒩_T(χ_oT₁)` equals its
   cut to the old disk `|z'| ≤ R√(5ν/6)` (`ms_oldPhys_eq_cut`) and is a separated, axisymmetric
   source with finite moment (`ms_sepFacts`).  Any representatives `g₁, g₂` of `χ_o(T₁,0)` agree
   with `oldThinTen T` `ageμ`-a.e. (`ms_rep_ae`), so the transition field of `g₁ + g₂` is
   `sepTrans S` (`WardX0Congr.sepW_congr`, `sepTrans_congr`).
2. **Pointwise domination** `|sepTrans S| ≤ P_ν transMaj(|S|)` (`TransSepDom`).
3. **Late output**: the velocity vanishes for `νs < 4/5`, so `‖g⁻¹M_Uv‖ ≤ Λ·(ungained)` on both
   receivers (`lrt_gainZ1_le`, `tt_gainHT_le`), `Λ ≥ g⁻¹` on the support.
4. **Thin receiver** (5346-5352): the chart majorant of `M_V` after the transition majorant,
   `ThinChart` (thin multiplication on the window, from the pointwise phase norm) and
   `TransMajPointMass` (new, below: `‖transMaj(y,·)‖_{L²_τ} ≤ P_νR^{-4}∫‖g(z,·)‖_{L²_τ}dz`, the
   pointwise version `q = ∞`, `p = 1` of `sep:young`, kernel `D^{-4}`).
5. **Repair receiver** (5333-5340): `RepChart` (`ρ_b^{-1/2}·R⁻¹·P_νρ`, Hölder against `L^{22/3}`)
   and `TransMajMassL223` (new, below: `‖transMaj‖_{L²_τL^{22/3}} ≤ P_νR^{-79/22}∫‖g(z,·)‖_{L²_τ}dz`,
   `sep:thin-global` with `q = 22/3` for the majorant).
6. **The mass** `∫‖S(z,·)‖_{L²_τ}dz ≤ πR²N₀` (`ChartMassLe`, `Annulus/Defs.lean`, 3729-3730,
   2685-2687; proved by `chartMassLe_of chartPhaseNorm`, tasks `PartIII-b:C/rep/4/2/org/3/3/2-3`),
   `N₀ = oldMass` (`oldMass_eq`).

Leaves and their tasks: `TransSepDom` (`PartIII-b:C/rep/5/2/2/12`), `TransMajFacts` (accepted),
`ThinChart`, `RepChart` (`PartIII-b:C/rep/4/4/1/org/3/2`, `/3/4`), `TransMajPointMass`,
`TransMajMassL223` (`PartIII-b:C/rep/4/2/org/3/4/1`, `/2`), `ChartMassLe`.

Exponents: thin `R^{-4}·R² = ε²`; repair `ε^{25/22}·ε^{79/22}·ε^{-2} = ε^{30/11} ≤ ε^{49/22}`
(`ε ≤ 1`).  The source's thin-to-repair entry `ε^{49/22}` uses the `L²` norm of the thin source
(5333-5335); the table here is stated through the mass `N₀`, and the `L¹` (mass) route of
`sep:thin-global` with `q = 22/3` gives the stronger power `ε^{30/11}`.

The hypothesis `AnnulusFieldBoundsAt` of `TransMultiplierStepAt` is not used (the majorant route
needs the pointwise phase norm on the thin receiver, which `AnnulusFieldBoundsAt`, `q ∈ {2,22/3}`,
does not provide).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The two kernel steps from the mass -/

/-- **The pointwise kernel step from the mass** (source 5346-5347: "The separated pointwise
velocity is at most `P_νε²s²N_0`"; 3640-3648, `sep:young` pointwise version `q = ∞`, here with
`p = 1`, kernel `sup_{|x| ≥ D}|x|^{-4-j} = D^{-4-j}`; 3683-3701: the cutoff correction and the
commutators cost `L^{-1}` per derivative of the cutoff, the stream primitive
`∫_r^∞ρ(ρ - r_o)^{-4}dρ ≤ C L^{-2}`; 5338-5340: "The outward stream primitive has the same norm
powers"): for `0 < ν ≤ 1`, `R ≥ 1`, `P > 0` and every jointly measurable `P`-periodic `g ≥ 0`
vanishing outside the old disk `ϱ ≤ R√(5ν/6)`, at **every** receiver `y`,
`‖transMaj ν R g (·, y)‖_{L²_τ} ≤ C ν^{-k} R^{-4} ∫ ‖g(·,z)‖_{L²_τ} dz`.
(Gap `D = R√ν(1 - √(5/6))`; order zero `D^{-4}`; order one `L⁻¹D^{-5} ≤ C ν^{-3}R^{-4}`, `R ≥ 1`;
primitive `L^{-2}·(L/D)D^{-2}`; Minkowski in `λ` and `z` (`IIIa.ltauAt_lintegral_le`) and phase
invariance (`IIIa.ltauAt_shift`).) -/
def TransMajPointMass : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (ν R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P →
    ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
      (∀ τ (z : Space), R * Real.sqrt (5 * ν / 6) < ϱ z → g τ z = 0) →
        ∀ y : Space, IIIa.ltauAt P (fun τ => transMaj ν R g τ y) ≤
          ENNReal.ofReal (C * ν⁻¹ ^ k * R ^ (-(4 : ℝ))) *
            ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z)

/-- **The `L^{22/3}` kernel step from the mass** (source 3669-3679 `sep:thin-global` with
`q = 22/3`: `R^{-2+3/q}N₀` for the physical mass `R²N₀`, i.e. the kernel `D^{-4+9/22} = D^{-79/22}`
against `∫‖T(z,·)‖_{L²_τ}dz`; 3683-3701: the same bound after the stream cutoff, the cutoff
majorant `CD^{-2}(D²+|z-z_src|²)^{-1}1_{|y'-z'_src| ≤ CD}`; 5333-5340): for `0 < ν ≤ 1`, `R ≥ 1`,
`P > 0` and every jointly measurable `P`-periodic `g ≥ 0` vanishing outside the old disk,
`‖transMaj ν R g‖_{L²_τL^{22/3}} ≤ C ν^{-k} R^{-79/22} ∫ ‖g(·,z)‖_{L²_τ} dz`.
(Order zero: `IIIa.SepDomYoung` with `p = 1`, `q = b = 22/3`, then Minkowski
`‖g‖_{L²_τL¹} ≤ ∫‖g(·,z)‖_{L²_τ}dz`; order one: `L⁻¹D^{-101/22} ≤ Cν^{-3}R^{-79/22}`; primitive:
`∫_L^∞ρ((ρ-r_o)²+h²)^{-2}dρ ≤ (L/D)(D²+h²)^{-1}/2`, `‖(D²+h²)^{-1}‖_{L^{22/3}(ℝ)} = CD^{-2+3/22}`,
the annulus area `πνR²/4`, times `L^{-2}`.) -/
def TransMajMassL223 : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (ν R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P →
    ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
      (∀ τ (z : Space), R * Real.sqrt (5 * ν / 6) < ϱ z → g τ z = 0) →
        IIIa.ltauLq P (22 / 3) (transMaj ν R g) ≤
          ENNReal.ofReal (C * ν⁻¹ ^ k * R ^ (-(79 / 22 : ℝ))) *
            ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z)

namespace MultStepOrg

/-! ## 2. The separated source of the old thin source -/

/-- A chart tensor vanishing for `νs ≤ 6/5` has a lift equal to its cut to the old disk
`|z'| ≤ R√(5ν/6)` (source 4163-4168). -/
theorem ms_oldPhys_eq_cut {ν ε c : ℝ} (hν : 0 < ν) (hε : 0 < ε) (G : Chart → Ten3)
    (hG0 : ∀ p : Chart, ν * p.1 ≤ 6 / 5 → G p = 0) (τ : ℝ) (z : Space) :
    oldPhys ε⁻¹ c G τ z = oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G τ z := by
  unfold oldCutSrc
  split_ifs with hz
  · rfl
  · have h0r : 0 ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := by positivity
    have hlt := not_le.1 hz
    have hpos : 0 < NearInst.hRad z := lt_of_le_of_lt h0r hlt
    have hsq : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 = ε⁻¹ ^ 2 * (5 * ν / 6) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hlt2 : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad z ^ 2 := by
      nlinarith
    have hs : ν * (NearInst.chartOf ε⁻¹ c z τ).1 ≤ 6 / 5 := by
      show ν * (ε⁻¹ ^ 2 / NearInst.hRad z ^ 2) ≤ 6 / 5
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have hG := hG0 _ hs
    simp only [oldPhys, NearInst.cartLift, hG, rb_nsSym_zero, smul_zero, Matrix.mul_zero,
      Matrix.zero_mul]

/-- The cut lift of a measurable chart tensor with finite moment is a separated axisymmetric
source of period `2εc` (source 4155-4171, 2684-2703; as in `thinSepBridge`). -/
theorem ms_sepFacts {ν ε c : ℝ} (hc : 0 < c) (hε : 0 < ε) (G : Chart → Ten3)
    (hGm : Measurable G) (hM : ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤) :
    IIIa.IsSepSource (2 * ε * c) (ε⁻¹ * Real.sqrt (5 * ν / 6))
        (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G) ∧
      SepMoment (2 * ε * c) (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G) ∧
      IsAxiSource (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G) := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hper : ∀ τ z, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G (τ + 2 * c / ε⁻¹) z =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G τ z := by
    intro τ z
    unfold oldCutSrc
    rw [oldPhysPeriodic ε⁻¹ c G τ z]
  have hper2 : ∀ τ z, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G (τ + 2 * ε * c) z =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G τ z := by
    intro τ z
    rw [hP]
    exact hper τ z
  have hsupp : ∀ τ z, ε⁻¹ * Real.sqrt (5 * ν / 6) < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) →
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G τ z = 0 := by
    intro τ z hz
    have hz' : ¬ NearInst.hRad z ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := not_le.2 hz
    unfold oldCutSrc
    simp only [hz', ite_false]
  have hsep : IIIa.IsSepSource (2 * ε * c) (ε⁻¹ * Real.sqrt (5 * ν / 6))
      (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G) :=
    { measurable := oldCutMeasurable ε⁻¹ c _ G hGm
      periodic := hper2
      support := hsupp }
  have hmom := oldCutMoment ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G hR hc hGm hM
  rw [← hP] at hmom
  have hAx : IsAxiSource (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G) := by
    unfold IsAxiSource
    refine ⟨fun co si hco τ z => ?_, fun τ z => ?_⟩
    · unfold oldCutSrc
      rw [rot_hRad co si hco z]
      split_ifs with hz
      · exact oldPhysRotEquiv co si hco ε⁻¹ c G τ z
      · simp
    · unfold oldCutSrc
      rw [refl_hRad z]
      split_ifs with hz
      · exact oldPhysReflEquiv ε⁻¹ c G τ z
      · simp
  exact ⟨hsep, hmom, hAx⟩

/-- **Representatives of the old thin source** (source 5148-5157): any representatives `g₁, g₂`
of `χ_o(T₁, 0)` sum to `oldThinTen T = χ̂_o(νs)T₁` for `ageμ c (-1/2)`-a.e. chart point. -/
theorem ms_rep_ae (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (hρ : 0 < L.ρb Pl K)
    (T : LStr Pl K L) {g₁ g₂ : Chart → Ten3} (hg : IsRep Pl K L (oldThin Pl K L T) g₁ g₂) :
    g₁ + g₂ =ᵐ[ageμ (cOf L.ν) (-1 / 2)] oldThinTen Pl K L T := by
  have h1 := wo_rep_ae hρ K.hχo (thinPart T) hg.1 hg.2
  have happ := chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo (thinPart T)
  have a1 := happ.1
  have a2 := happ.2
  have hf : (thinPart T).fst = T.fst := by simp [thinPart]
  have hs : (thinPart T).snd = 0 := by simp [thinPart]
  rw [hf] at a1
  rw [hs] at a2
  have z0 := Lp.coeFn_zero Ten3 2 (gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν)
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at a1
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at a2 z0
  filter_upwards [h1, a1, a2, z0] with p e1 e2 e3 e4
  rw [e1]
  show ((oldThin Pl K L T).fst : Chart → Ten3) p + ((oldThin Pl K L T).snd : Chart → Ten3) p =
    K.χo (L.ν * p.1) • (T.fst : Chart → Ten3) p
  rw [e2, e3, e4]
  simp [cutFun]

/-! ## 3. Bookkeeping -/

theorem ms_pow_le {x : ℝ} (hx : 1 ≤ x) {a b c K : ℕ} (h : a + b + c ≤ K) :
    x ^ a * x ^ b * x ^ c ≤ x ^ K := by
  rw [← pow_add, ← pow_add]
  exact pow_le_pow_right₀ hx h

theorem ms_mono {a X Y b c d : ℝ} (h : X ≤ Y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) : a * X * b * c * d ≤ a * Y * b * c * d := by
  have h1 := mul_le_mul_of_nonneg_left h ha
  have h2 := mul_le_mul_of_nonneg_right h1 hb
  have h3 := mul_le_mul_of_nonneg_right h2 hc
  exact mul_le_mul_of_nonneg_right h3 hd

theorem ms_mono3 {a b X Y c d : ℝ} (h : X ≤ Y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) : a * b * X * c * d ≤ a * b * Y * c * d := by
  have h1 := mul_le_mul_of_nonneg_left h (mul_nonneg ha hb)
  have h3 := mul_le_mul_of_nonneg_right h1 hc
  exact mul_le_mul_of_nonneg_right h3 hd

/-- Thin receiver: `R^{-4}·R² = ε²`, `R = ε⁻¹` (source 5346-5352). -/
theorem ms_e4 {ε : ℝ} (hε : 0 < ε) : ε⁻¹ ^ (-(4 : ℝ)) * ε⁻¹ ^ 2 = ε ^ (2 : ℝ) := by
  rw [tt_inv_rpow_neg hε]
  have h1 : ε ^ (4 : ℝ) = ε ^ (2 : ℝ) * ε ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hε]; norm_num
  rw [h1, mul_assoc, ← mul_pow, mul_inv_cancel₀ hε.ne', one_pow, mul_one]

/-- Repair receiver: `ε^{25/22}·R^{-79/22}·R² = ε^{30/11} ≤ ε^{49/22}` for `0 < ε ≤ 1` (source
5329-5335). -/
theorem ms_e79 {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ (25 / 22 : ℝ) * (ε⁻¹ ^ (-(79 / 22 : ℝ)) * ε⁻¹ ^ 2) ≤ ε ^ (49 / 22 : ℝ) := by
  rw [tt_inv_rpow_neg hε]
  have h1 : ε ^ (25 / 22 : ℝ) * ε ^ (79 / 22 : ℝ) = ε ^ (30 / 11 : ℝ) * ε ^ 2 := by
    rw [← Real.rpow_add hε, ← Real.rpow_natCast, ← Real.rpow_add hε]; norm_num
  have e : ε ^ (25 / 22 : ℝ) * (ε ^ (79 / 22 : ℝ) * ε⁻¹ ^ 2) = ε ^ (30 / 11 : ℝ) := by
    calc ε ^ (25 / 22 : ℝ) * (ε ^ (79 / 22 : ℝ) * ε⁻¹ ^ 2)
        = (ε ^ (25 / 22 : ℝ) * ε ^ (79 / 22 : ℝ)) * ε⁻¹ ^ 2 := by ring
      _ = ε ^ (30 / 11 : ℝ) := by
        rw [h1, mul_assoc, ← mul_pow, mul_inv_cancel₀ hε.ne', one_pow, mul_one]
  rw [e]
  exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num)

/-! ## 4. The multiplier step at one level -/

/-- **The multiplier step at one level** (source 5312-5352, 3669-3701, 3729-3730), `k₁ = 0`, from
the pointwise domination of the transitions, the two window multiplications, the two kernel
steps from the mass and the physical mass of the lift. -/
theorem ms_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1)
    (hnear : NearAt Pl K L μ)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb)
    (hF : TransMajFacts) (hMass : ChartMassLe)
    {Cd : ℝ} {kd : ℕ} (hCd : 0 ≤ Cd)
    (hDom : ∀ S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) S →
      SepMoment (2 * L.ε * cOf L.ν) S → IsAxiSource S → ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
        ‖sepTrans L.ν μ L.ε⁻¹ K.χy S τ y‖ₑ ≤
          ENNReal.ofReal (Cd * L.ν⁻¹ ^ kd) * transMaj L.ν L.ε⁻¹ (IIIa.srcNorm S) τ y)
    {Ct : ℝ} {kt : ℕ} (hCt : 0 ≤ Ct)
    (hThin : ∀ (f : ℝ → Space → ℝ≥0∞) (A : ℝ≥0∞), ChartGood (2 * L.ε * cOf L.ν) f →
      (∀ τ (y : Space), y ∉ streamAnn L.ν L.ε⁻¹ → f τ y = 0) →
      (∀ y : Space, IIIa.ltauAt (2 * L.ε * cOf L.ν) (fun τ => f τ y) ≤ A) →
        z1Maj (cOf L.ν) K.mZ (multMaj L.ε⁻¹ L.V f) ≤ ENNReal.ofReal (Ct * L.ν⁻¹ ^ kt) * A)
    {Cr : ℝ} {kr : ℕ} (hCr : 0 ≤ Cr)
    (hRep : ∀ f : ℝ → Space → ℝ≥0∞, ChartGood (2 * L.ε * cOf L.ν) f →
      (∀ τ (y : Space), y ∉ streamAnn L.ν L.ε⁻¹ → f τ y = 0) →
        htMaj (cOf L.ν) (L.ρb Pl K) (multMaj L.ε⁻¹ L.rb f) ≤
          ENNReal.ofReal (Cr * L.ν⁻¹ ^ kr * L.ε ^ (25 / 22 : ℝ) * Real.exp (K.m0 / 2 / L.ν)) *
            IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 3) f)
    {Cp : ℝ} {kp : ℕ} (hCp : 0 ≤ Cp)
    (hP : ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) →
      (∀ τ z, g (τ + 2 * L.ε * cOf L.ν) z = g τ z) →
      (∀ τ (z : Space), L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) < ϱ z → g τ z = 0) →
        ∀ y : Space, IIIa.ltauAt (2 * L.ε * cOf L.ν) (fun τ => transMaj L.ν L.ε⁻¹ g τ y) ≤
          ENNReal.ofReal (Cp * L.ν⁻¹ ^ kp * L.ε⁻¹ ^ (-(4 : ℝ))) *
            ∫⁻ z : Space, IIIa.ltauAt (2 * L.ε * cOf L.ν) (fun τ => g τ z))
    {Cq : ℝ} {kq : ℕ} (hCq : 0 ≤ Cq)
    (hQ : ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) →
      (∀ τ z, g (τ + 2 * L.ε * cOf L.ν) z = g τ z) →
      (∀ τ (z : Space), L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) < ϱ z → g τ z = 0) →
        IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 3) (transMaj L.ν L.ε⁻¹ g) ≤
          ENNReal.ofReal (Cq * L.ν⁻¹ ^ kq * L.ε⁻¹ ^ (-(79 / 22 : ℝ))) *
            ∫⁻ z : Space, IIIa.ltauAt (2 * L.ε * cOf L.ν) (fun τ => g τ z))
    (Cf : ℝ) (kf : ℕ) :
    TransMultiplierStepAt Pl K L μ 0 (2 * Cd * (Ct * Cp + Cr * Cq) * Real.pi)
      (kd + kt + kp + kr + kq) Cf kf := by
  intro T g₁ g₂ hg _hfield hfin Λ hΛ0 hΛ v hvs hv
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hR0 : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hι0 : 0 ≤ L.ν⁻¹ := inv_nonneg.2 hν.le
  have hι : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hρb : 0 < L.ρb Pl K := by
    unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
    have h1 := (L.params Pl).ν_pos
    have h2 := (L.params Pl).ε_pos
    exact mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 (pow_pos h1 _))) (Real.exp_pos _))
      (Real.rpow_pos_of_pos h2 _)
  -- the chart tensor of the old thin source and its separated lift
  obtain ⟨G, hGdef⟩ : ∃ G : Chart → Ten3, G = oldThinTen Pl K L T := ⟨_, rfl⟩
  have hGm : Measurable G := hGdef ▸ measurable_oldThinTen Pl K L T
  have hG0 : ∀ p : Chart, L.ν * p.1 ≤ 6 / 5 → G p = 0 := by
    intro p hp
    rw [hGdef]
    simp [oldThinTen, K.hχo.zero _ hp]
  have hrep : g₁ + g₂ =ᵐ[ageμ (cOf L.ν) (-1 / 2)] G := hGdef ▸ ms_rep_ae Pl K L hρb T hg
  have hM2 : ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ := by
    have h0 := strChartL2 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρb hmZ hν
      (oldThin Pl K L T)
    have hae : ((oldThin Pl K L T).fst : Chart → Ten3) + ((oldThin Pl K L T).snd : Chart → Ten3)
        =ᵐ[ageμ (cOf L.ν) (-1 / 2)] G :=
      hGdef ▸ ms_rep_ae Pl K L hρb T ⟨EventuallyEq.rfl, EventuallyEq.rfl⟩
    have e : ∫⁻ p, ‖strSum (oldThin Pl K L T) p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) =
        ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) :=
      lintegral_congr_ae (hae.mono fun p hp => by
        show ‖((oldThin Pl K L T).fst : Chart → Ten3) p +
          ((oldThin Pl K L T).snd : Chart → Ten3) p‖ₑ ^ 2 = ‖G p‖ₑ ^ 2
        rw [← hp]; rfl)
    rw [← e]
    exact h0
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      S = oldCutSrc L.ε⁻¹ (cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) G := ⟨_, rfl⟩
  obtain ⟨hS1, hS2, hS3⟩ := ms_sepFacts hc hε G hGm hM2
  rw [← hSdef] at hS1 hS2 hS3
  have hSeq : ∀ τ z, oldPhys L.ε⁻¹ (cOf L.ν) G τ z = S τ z := by
    intro τ z
    rw [hSdef]
    exact ms_oldPhys_eq_cut hν hε G hG0 τ z
  -- the transition field of the representatives is `sepTrans S`
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hrep)
  have hF' : transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂) =
      sepTrans L.ν μ L.ε⁻¹ K.χy S := by
    rw [transField_eq_sepTrans]
    refine sepTrans_congr (fun μ' y τ => ?_)
    rw [WardX0Congr.sepW_congr L.ν μ' hR0 hc (g₁ + g₂) G N hNm hN0 hsub τ y,
      show oldPhys L.ε⁻¹ (cOf L.ν) G = S from funext fun τ' => funext fun z => hSeq τ' z]
  have hcoef : (v : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy S) := by
    rw [← hF']; exact hv
  -- a.e. facts on the chart measures
  have h3a : ∀ᵐ p ∂(ageμ (cOf L.ν) (-3 / 2)), ((v : Chart → Merid) p =
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy S) p ∧ 0 < p.1) ∧
      (¬(4 / 5 ≤ L.ν * p.1 ∧ L.ν * p.1 ≤ 1) → (v : Chart → Merid) p = 0) := by
    rw [← NearInst.ae_bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
    exact (hcoef.and (bodyMeasure_ae_pos _ _ _)).and hvs
  have h3b : ∀ᵐ p ∂(z1Measure (cOf L.ν) K.mZ), ((v : Chart → Merid) p =
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy S) p ∧ 0 < p.1) ∧
      (¬(4 / 5 ≤ L.ν * p.1 ∧ L.ν * p.1 ≤ 1) → (v : Chart → Merid) p = 0) :=
    (NearInst.CoeffMult.z1_ac hc K.mZ).ae_le h3a
  have h3h : ∀ᵐ p ∂(htRhoMeasure (cOf L.ν) (L.ρb Pl K)), ((v : Chart → Merid) p =
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy S) p ∧ 0 < p.1) ∧
      (¬(4 / 5 ≤ L.ν * p.1 ∧ L.ν * p.1 ≤ 1) → (v : Chart → Merid) p = 0) := by
    rw [NearInst.ae_htRhoMeasure hρb, ← NearInst.ae_z1Measure _ K.mZ]; exact h3b
  have h3z : ∀ᵐ p ∂(gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν), ((v : Chart → Merid) p =
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy S) p ∧ 0 < p.1) ∧
      (¬(4 / 5 ≤ L.ν * p.1 ∧ L.ν * p.1 ≤ 1) → (v : Chart → Merid) p = 0) := by
    rw [NearInst.ae_gainZ1Measure]; exact h3b
  have h3g : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν),
      ((v : Chart → Merid) p = coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy S) p ∧ 0 < p.1) ∧
      (¬(4 / 5 ≤ L.ν * p.1 ∧ L.ν * p.1 ≤ 1) → (v : Chart → Merid) p = 0) := by
    rw [NearInst.ae_gainHTMeasure]; exact h3h
  -- the exact multiplier
  have hEx : IsExactMultiplier (concreteBase Pl K L μ hnear) L.ε⁻¹ L.V L.rb :=
    concreteBase_isExactMultiplier (h := hnear) NearInst.multPinOfLink hs
  have m1 : ((multOp Pl K L v).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ
      (gRate Pl) L.ν] fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
        (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p) ((v : Chart → Merid) p)) :=
    (hEx v).1
  have m2 : ((multOp Pl K L v).snd : Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν)
      (L.ρb Pl K) (gRate Pl) L.ν] fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
        (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.rb p) ((v : Chart → Merid) p)) :=
    (hEx v).2
  -- vanishing on young output
  have hlt : ∀ p : Chart, p.1 < 4 / 5 / L.ν → ¬(4 / 5 ≤ L.ν * p.1 ∧ L.ν * p.1 ≤ 1) := by
    intro p hp h
    have h' : 4 / 5 ≤ p.1 * L.ν := by rw [mul_comm]; exact h.1
    exact absurd ((div_le_iff₀ hν).2 h') (not_le.2 hp)
  have s1 : ∀ᵐ p ∂(gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν), p.1 < 4 / 5 / L.ν →
      ((multOp Pl K L v).fst : Chart → Ten3) p = 0 := by
    filter_upwards [m1, h3z] with p e1 e2 hp
    rw [e1, e2.2 (hlt p hp)]
    exact tt_ten3_symOuter_zero _
  have s2 : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν), p.1 < 4 / 5 / L.ν →
      ((multOp Pl K L v).snd : Chart → Ten3) p = 0 := by
    filter_upwards [m2, h3g] with p e1 e2 hp
    rw [e1, e2.2 (hlt p hp)]
    exact tt_ten3_symOuter_zero _
  -- late output: `g⁻¹ ≤ Λ` on the support (source 5317-5318)
  have hgΛ : ∀ p : Chart, 4 / 5 / L.ν ≤ p.1 → ginv (gRate Pl) L.ν p ≤ Λ := by
    intro p hp
    exact hΛ p (by rw [mul_comm]; exact (div_le_iff₀ hν).1 hp)
  have G1 := lrt_gainZ1_le hΛ0 hgΛ (multOp Pl K L v).fst s1
  have G2 := tt_gainHT_le hΛ0 hgΛ (multOp Pl K L v).snd s2
  -- the ungained receivers below the chart majorants
  have hK0 : 0 ≤ Cd * L.ν⁻¹ ^ kd := mul_nonneg hCd (pow_nonneg hι0 _)
  have Z1 : z1Ung (cOf L.ν) K.mZ ((multOp Pl K L v).fst : Chart → Ten3) ≤
      ENNReal.ofReal (2 * (Cd * L.ν⁻¹ ^ kd)) *
        z1Maj (cOf L.ν) K.mZ (multMaj L.ε⁻¹ L.V (transMaj L.ν L.ε⁻¹ (IIIa.srcNorm S))) := by
    unfold z1Ung z1Maj
    refine tt_L2_le (z1Measure (cOf L.ν) K.mZ) ?_
    have m1z : ∀ᵐ p ∂(z1Measure (cOf L.ν) K.mZ), ((multOp Pl K L v).fst : Chart → Ten3) p =
        NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
          (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p) ((v : Chart → Merid) p)) := by
      rw [← NearInst.ae_gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]; exact m1
    filter_upwards [m1z, h3b] with p e1 e2
    rw [e1, e2.1.1]
    exact tt_pt_le _ _ _ p hK0 (hDom S hS1 hS2 hS3 _ _
      (by rw [ϱ_chartY hR0 e2.1.2]; exact div_pos hR0 (Real.sqrt_pos.2 e2.1.2)))
  have H1 : htUng (cOf L.ν) (L.ρb Pl K) ((multOp Pl K L v).snd : Chart → Ten3) ≤
      ENNReal.ofReal (2 * (Cd * L.ν⁻¹ ^ kd)) *
        htMaj (cOf L.ν) (L.ρb Pl K) (multMaj L.ε⁻¹ L.rb
          (transMaj L.ν L.ε⁻¹ (IIIa.srcNorm S))) := by
    unfold htUng htMaj
    refine tt_L2_le (htRhoMeasure (cOf L.ν) (L.ρb Pl K)) ?_
    have m2z : ∀ᵐ p ∂(htRhoMeasure (cOf L.ν) (L.ρb Pl K)),
        ((multOp Pl K L v).snd : Chart → Ten3) p =
        NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
          (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.rb p) ((v : Chart → Merid) p)) := by
      rw [← NearInst.ae_gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]; exact m2
    filter_upwards [m2z, h3h] with p e1 e2
    rw [e1, e2.1.1]
    exact tt_pt_le _ _ _ p hK0 (hDom S hS1 hS2 hS3 _ _
      (by rw [ϱ_chartY hR0 e2.1.2]; exact div_pos hR0 (Real.sqrt_pos.2 e2.1.2)))
  -- the majorant: chart facts, kernel steps
  have hPpos : 0 < 2 * L.ε * cOf L.ν := by positivity
  obtain ⟨hGood, hvan⟩ := tt_transMaj_good hF hν hR0 hPpos hS1 hS3
  obtain ⟨f1, f2, f3⟩ := tt_srcNorm_facts hS1
  -- the physical mass (source 3729-3730, 2685-2687)
  set N0r := (oldMass Pl K L T).toReal with hN0r
  have hN0 : 0 ≤ N0r := ENNReal.toReal_nonneg
  have hMass' : ∫⁻ z : Space, IIIa.ltauAt (2 * L.ε * cOf L.ν) (fun τ => IIIa.srcNorm S τ z) ≤
      ENNReal.ofReal (Real.pi * L.ε⁻¹ ^ 2 * N0r) := by
    have h := hMass L.ε⁻¹ (cOf L.ν) hR0 hc G hGm
    have hPeq : 2 * cOf L.ν / L.ε⁻¹ = 2 * L.ε * cOf L.ν := by rw [div_inv_eq_mul]; ring
    have hmeq : oldMassAt (cOf L.ν) 0 (fun p => Ten3.toMatrix (G p)) = oldMass Pl K L T := by
      rw [hGdef, oldMass_eq]
    rw [hPeq, hmeq] at h
    have e : (∫⁻ z : Space, IIIa.ltauAt (2 * L.ε * cOf L.ν) (fun τ => IIIa.srcNorm S τ z)) =
        ∫⁻ z : Space, IIIa.ltauAt (2 * L.ε * cOf L.ν)
          (fun τ => IIIa.srcNorm (NearInst.cartLift L.ε⁻¹ (cOf L.ν) G) τ z) := by
      congr 1; funext z; congr 1; funext τ
      unfold IIIa.srcNorm
      rw [← hSeq τ z]; rfl
    rw [e]
    refine h.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by positivity)]
  -- thin receiver
  have hAp : 0 ≤ Cp * L.ν⁻¹ ^ kp * L.ε⁻¹ ^ (-(4 : ℝ)) :=
    mul_nonneg (mul_nonneg hCp (pow_nonneg hι0 _)) (Real.rpow_nonneg hR0.le _)
  have T3 := hThin _ _ hGood hvan (hP _ f1 f2 f3)
  have T4 : ENNReal.ofReal (Cp * L.ν⁻¹ ^ kp * L.ε⁻¹ ^ (-(4 : ℝ))) *
      ∫⁻ z : Space, IIIa.ltauAt (2 * L.ε * cOf L.ν) (fun τ => IIIa.srcNorm S τ z) ≤
      ENNReal.ofReal (Cp * L.ν⁻¹ ^ kp * L.ε⁻¹ ^ (-(4 : ℝ)) * (Real.pi * L.ε⁻¹ ^ 2 * N0r)) := by
    rw [ENNReal.ofReal_mul hAp]
    exact mul_le_mul' le_rfl hMass'
  have he2 : 0 ≤ 2 * (Cd * L.ν⁻¹ ^ kd) := mul_nonneg zero_le_two hK0
  have hX : 0 ≤ Real.pi * L.ε⁻¹ ^ 2 * N0r := by positivity
  have ha := tt_chain G1 Z1 T3 T4 hΛ0 he2 (mul_nonneg hCt (pow_nonneg hι0 _))
    (mul_nonneg hAp hX)
  -- repair receiver
  have hAq : 0 ≤ Cq * L.ν⁻¹ ^ kq * L.ε⁻¹ ^ (-(79 / 22 : ℝ)) :=
    mul_nonneg (mul_nonneg hCq (pow_nonneg hι0 _)) (Real.rpow_nonneg hR0.le _)
  have R3 := hRep _ hGood hvan
  have R4 : IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 3) (transMaj L.ν L.ε⁻¹ (IIIa.srcNorm S)) ≤
      ENNReal.ofReal (Cq * L.ν⁻¹ ^ kq * L.ε⁻¹ ^ (-(79 / 22 : ℝ)) *
        (Real.pi * L.ε⁻¹ ^ 2 * N0r)) := by
    refine (hQ _ f1 f2 f3).trans ?_
    rw [ENNReal.ofReal_mul hAq]
    exact mul_le_mul' le_rfl hMass'
  have hAr : 0 ≤ Cr * L.ν⁻¹ ^ kr * L.ε ^ (25 / 22 : ℝ) * Real.exp (K.m0 / 2 / L.ν) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCr (pow_nonneg hι0 _)) (Real.rpow_nonneg hε.le _))
      (Real.exp_pos _).le
  have hb := tt_chain G2 H1 R3 R4 hΛ0 he2 hAr (mul_nonneg hAq hX)
  -- bookkeeping
  have hk1 : L.ν⁻¹ ^ kd * L.ν⁻¹ ^ kt * L.ν⁻¹ ^ kp ≤ L.ν⁻¹ ^ (kd + kt + kp + kr + kq) :=
    ms_pow_le hι (by omega)
  have hk2 : L.ν⁻¹ ^ kd * L.ν⁻¹ ^ kr * L.ν⁻¹ ^ kq ≤ L.ν⁻¹ ^ (kd + kt + kp + kr + kq) :=
    ms_pow_le hι (by omega)
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hfst : ‖(multOp Pl K L v).fst‖ ≤ (2 * Cd * (Ct * Cp) * Real.pi) *
      L.ν⁻¹ ^ (kd + kt + kp + kr + kq) * L.ε ^ (2 : ℝ) * Λ * N0r := by
    calc ‖(multOp Pl K L v).fst‖ ≤ _ := ha
      _ = (2 * Cd * (Ct * Cp) * Real.pi) * (L.ν⁻¹ ^ kd * L.ν⁻¹ ^ kt * L.ν⁻¹ ^ kp) *
            (L.ε⁻¹ ^ (-(4 : ℝ)) * L.ε⁻¹ ^ 2) * Λ * N0r := by ring
      _ = (2 * Cd * (Ct * Cp) * Real.pi) * (L.ν⁻¹ ^ kd * L.ν⁻¹ ^ kt * L.ν⁻¹ ^ kp) *
            L.ε ^ (2 : ℝ) * Λ * N0r := by rw [ms_e4 hε]
      _ ≤ _ := ms_mono hk1
            (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hCd) (mul_nonneg hCt hCp)) hpi)
            (Real.rpow_nonneg hε.le _) hΛ0 hN0
  have hexp : Real.exp (K.m0 / 2 / L.ν) = Real.exp (K.m0 / (2 * L.ν)) := by rw [div_div]
  have hE : 0 ≤ Real.exp (K.m0 / (2 * L.ν)) := (Real.exp_pos _).le
  have hB' : 0 ≤ L.ε ^ (49 / 22 : ℝ) * Real.exp (K.m0 / (2 * L.ν)) :=
    mul_nonneg (Real.rpow_nonneg hε.le _) hE
  have hsnd : ‖(multOp Pl K L v).snd‖ ≤ (2 * Cd * (Cr * Cq) * Real.pi) *
      L.ν⁻¹ ^ (kd + kt + kp + kr + kq) *
        (L.ε ^ (49 / 22 : ℝ) * Real.exp (K.m0 / (2 * L.ν))) * Λ * N0r := by
    calc ‖(multOp Pl K L v).snd‖ ≤ _ := hb
      _ = (2 * Cd * (Cr * Cq) * Real.pi) * (L.ν⁻¹ ^ kd * L.ν⁻¹ ^ kr * L.ν⁻¹ ^ kq) *
            ((L.ε ^ (25 / 22 : ℝ) * (L.ε⁻¹ ^ (-(79 / 22 : ℝ)) * L.ε⁻¹ ^ 2)) *
              Real.exp (K.m0 / (2 * L.ν))) * Λ * N0r := by rw [hexp]; ring
      _ ≤ (2 * Cd * (Cr * Cq) * Real.pi) * (L.ν⁻¹ ^ kd * L.ν⁻¹ ^ kr * L.ν⁻¹ ^ kq) *
            (L.ε ^ (49 / 22 : ℝ) * Real.exp (K.m0 / (2 * L.ν))) * Λ * N0r :=
          ms_mono3 (mul_le_mul_of_nonneg_right (ms_e79 hε hε1) hE)
            (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hCd) (mul_nonneg hCr hCq)) hpi)
            (by positivity) hΛ0 hN0
      _ ≤ _ := ms_mono hk2
            (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hCd) (mul_nonneg hCr hCq)) hpi)
            hB' hΛ0 hN0
  have hA : 0 ≤ L.ε ^ (2 : ℝ) := Real.rpow_nonneg hε.le _
  have hB : 0 ≤ L.ε ^ (49 / 22 : ℝ) * Real.exp (K.m0 / (2 * L.ν)) := by positivity
  have hW : 0 ≤ 2 * Cd * Real.pi * L.ν⁻¹ ^ (kd + kt + kp + kr + kq) * Λ * N0r :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hCd) hpi)
      (pow_nonneg hι0 _)) hΛ0) hN0
  have c1 : 0 ≤ (2 * Cd * Real.pi * L.ν⁻¹ ^ (kd + kt + kp + kr + kq) * Λ * N0r) * (Ct * Cp) *
      (L.ε ^ (49 / 22 : ℝ) * Real.exp (K.m0 / (2 * L.ν))) :=
    mul_nonneg (mul_nonneg hW (mul_nonneg hCt hCp)) hB
  have c2 : 0 ≤ (2 * Cd * Real.pi * L.ν⁻¹ ^ (kd + kt + kp + kr + kq) * Λ * N0r) * (Cr * Cq) *
      L.ε ^ (2 : ℝ) :=
    mul_nonneg (mul_nonneg hW (mul_nonneg hCr hCq)) hA
  rw [WithLp.prod_norm_eq_of_L1, pow_zero]
  have e : 2 * Cd * (Ct * Cp + Cr * Cq) * Real.pi * L.ν⁻¹ ^ (kd + kt + kp + kr + kq) * 1 *
      (L.ε ^ (2 : ℝ) + L.ε ^ (49 / 22 : ℝ) * Real.exp (K.m0 / (2 * L.ν))) * Λ * N0r =
      (2 * Cd * (Ct * Cp) * Real.pi) * L.ν⁻¹ ^ (kd + kt + kp + kr + kq) * L.ε ^ (2 : ℝ) * Λ *
          N0r +
        (2 * Cd * (Cr * Cq) * Real.pi) * L.ν⁻¹ ^ (kd + kt + kp + kr + kq) *
          (L.ε ^ (49 / 22 : ℝ) * Real.exp (K.m0 / (2 * L.ν))) * Λ * N0r +
        ((2 * Cd * Real.pi * L.ν⁻¹ ^ (kd + kt + kp + kr + kq) * Λ * N0r) * (Ct * Cp) *
          (L.ε ^ (49 / 22 : ℝ) * Real.exp (K.m0 / (2 * L.ν))) +
         (2 * Cd * Real.pi * L.ν⁻¹ ^ (kd + kt + kp + kr + kq) * Λ * N0r) * (Cr * Cq) *
          L.ε ^ (2 : ℝ)) := by ring
  rw [e]
  linarith [hfst, hsnd, c1, c2]

end MultStepOrg

/-! ## 5. Along the sequence -/

/-- **The multiplier step along the sequence** (source 5312-5352, 3669-3701, 3729-3730), with the
`S`-degree `k₁ = 0`: from `TransSepDom` (pointwise domination), `TransMajFacts`, `ThinChart` and
`RepChart` (the two window multiplications), `TransMajPointMass` and `TransMajMassL223` (the
kernel steps from the mass) and `ChartMassLe` (the physical mass of the lift). -/
theorem transMultiplierStep_of {Pl : PlanarData} {σ₀ mZ dm dp : ℝ} (hD : TransSepDom)
    (hF : TransMajFacts) (hT : ThinChart dm dp) (hR : RepChart dm dp) (hP : TransMajPointMass)
    (hQ : TransMajMassL223) (hM : ChartMassLe) : TransMultiplierStep Pl σ₀ mZ dm dp := by
  refine ⟨0, fun D _ _ _ hst Cf kf => ?_⟩
  have hσ' : -(1 / 4 : ℝ) < D.σ₀ / 2 := by linarith [hst.sigma_pos]
  obtain ⟨Cd, kd, hCd, hDd⟩ := hD (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) hσ' D.K.χy hst.chiY
  obtain ⟨Ct, kt, hCt, hTt⟩ := hT D hst
  obtain ⟨Cr, kr, hCr, hRr⟩ := hR D hst
  obtain ⟨Cp, kp, hCp, hPp⟩ := hP
  obtain ⟨Cq, kq, hCq, hQq⟩ := hQ
  refine ⟨2 * Cd * (Ct * Cp + Cr * Cq) * Real.pi, kd + kt + kp + kr + kq,
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hCd)
      (add_nonneg (mul_nonneg hCt hCp) (mul_nonneg hCr hCq))) Real.pi_pos.le, ?_⟩
  have hev1 := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hev1, hev2, hst.pins, hst.near, hTt, hRr] with n e1 e2 pins near ht hr z hz
  have hν := (D.level n).ν_pos
  have hε := (D.level n).ε_pos
  have hR1 : 1 ≤ (D.level n).ε⁻¹ := (one_le_inv₀ hε).2 e2.2
  have hPpos : 0 < 2 * (D.level n).ε * cOf (D.level n).ν := by
    have := cOf_pos hν; positivity
  exact MultStepOrg.ms_level D.Pl D.K (D.level n) (D.mu n z) hst.C0_pos
    (by linarith [hst.mZ_gt]) e2.1 e2.2 (near z hz) (pins z hz).split hF hM hCd
    (fun S hS1 hS2 hS3 τ y hy => hDd _ _ _ _ hν e2.1 hR1 hPpos (e1 z hz) S hS1 hS2 hS3 τ y hy)
    hCt ht hCr hr hCp
    (fun g g1 g2 g3 y => hPp _ _ _ hν e2.1 hR1 hPpos g g1 g2 g3 y) hCq
    (fun g g1 g2 g3 => hQq _ _ _ hν e2.1 hR1 hPpos g g1 g2 g3) Cf kf

end UnforcedLeray.Short.PartIIIb.Concrete
