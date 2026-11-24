import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.Gain

/-!
# `PartIII-b:C/rep/4/4/1/org/3/org` (b): the separated-kernel entries of the transition table

Source `the November 2 reference manuscript` 5312-5316 (both transitions, support
`0.8/ν < s < 1/ν`), 5322-5333 (the repair-source row: thin receiver `ε^{63/22}e^{m₀/ν}`, scaled
repair receiver `ε^{79/22}e^{3m₀/(2ν)}`, common `P_νS^k`, factor `G(w)|N_ν|e^{-4γ/(9ν)}` on late
output), 5337-5339 ("The repair-to-thin entry uses the pointwise exponent `79/22`, followed by `ρR`.
The repair-to-repair entry uses the source `L^{22/19}` norm and the `L^{11/3}` kernel"), 5339-5341
("The outward stream primitive has the same norm powers, so both transition terms have the
late-output bound"), 5134-5139 (`‖r_b‖_{C_τL^{11/4}} ≤ P_νρ`), 2697-2719 (`Z₁`, `V_m(s)`), 3631-3647
(`sep:young` and its pointwise form), 4176-4194 (the outward primitive).

The transition field of the separated representative `T` of the old repair source is dominated
by the transition majorant `transMaj` (`TransSepDom`, `Sub/PartIII-b_C_rep_5_2_2TransOrg.lean`:
order-zero and order-one gap majorants `sepDom` on the annulus `R√ν ≤ ϱ ≤ R√(5ν/4)` and the
outward-primitive majorant `outMaj`, with the cutoff factors `1`, `L⁻¹`, `L⁻²`, `L = R√ν`).  After
`M_U` the two receivers see the chart majorant `multMaj R A transMaj` (`A = V` resp. `A = r_b`).
The two entries, without the output gain and before the product estimate `repair:source`, are:

* **`TransMajThin`** (thin receiver): `‖multMaj R V transMaj‖_{Z₁} ≤ P_ν ε^{79/22} ‖T‖_{L²_τL^{22/19}}`;
  composed (`transMajThinAt_of`, proved) of the pointwise exponent (`TransMajPointL2`, generic:
  `‖transMaj(y,·)‖_{L²_τ} ≤ P_ν R^{-79/22}‖g‖_{L²_τL^{22/19}}` at every receiver) and the thin
  multiplication on the window (`ThinChart`: `q`-cells are one period, Hölder in `η` with `V_m(s)`).
* **`TransMajRep`** (repair receiver): `‖multMaj R r_b transMaj‖_{ρ_b^{-1/2}H_T} ≤
  P_ν ε^{95/22}e^{m₀/(2ν)} ‖T‖_{L²_τL^{22/19}}`; composed (`transMajRepAt_of`, proved) of the
  `L^{11/3}` kernel (`TransMajL223`, generic: `‖transMaj‖_{L²_τL^{22/3}} ≤ P_ν R^{-35/11}‖g‖`) and
  the repair multiplication (`RepChart`: chart-to-physical, Hölder `1/2 = 4/11 + 3/22` with
  `‖r_b‖_{C_τL^{11/4}} ≤ P_νρ`, `ρ/√ρ_b = P_ν ε^{3/22}e^{m₀/(2ν)}`, normalization `R⁻¹ = ε`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The two entries used by the table -/

namespace SeqData

variable (D : SeqData)

/-- **Thin receiver, separated kernel, both transitions** (source 5323-5338: repair source → thin
receiver, "the pointwise exponent `79/22`"; 5339-5341: the outward primitive has the same norm
powers; 2697, 2717: `Z₁` and `V_m(s)`): for large `n`, every separated axisymmetric source `T`
(period `2εc`, old disk `|z'| ≤ ε⁻¹√(5ν/6)`), the `Z₁` norm without the gain of the chart majorant
of `M_V` applied to the transition majorant is at most `P_ν ε^{79/22}‖T‖_{L²_τL^{22/19}}`. -/
def TransMajThinAt : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * (D.level n).ε * cOf (D.level n).ν)
          ((D.level n).ε⁻¹ * Real.sqrt (5 * (D.level n).ν / 6)) T →
        SepMoment (2 * (D.level n).ε * cOf (D.level n).ν) T → IsAxiSource T →
        z1Maj (cOf (D.level n).ν) D.K.mZ (multMaj (D.level n).ε⁻¹ (D.level n).V
            (transMaj (D.level n).ν (D.level n).ε⁻¹ (IIIa.srcNorm T))) ≤
          ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (79 / 22 : ℝ)) *
            IIIa.ltauLq (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19) (IIIa.srcNorm T)

/-- **Scaled repair receiver, separated kernel, both transitions** (source 5323-5339: repair
source → scaled repair receiver, "the source `L^{22/19}` norm and the `L^{11/3}` kernel";
5339-5341; 5134-5139; 2698-2700): for large `n` and every separated axisymmetric source `T`, the
`ρ_b^{-1/2}H_T` norm without the gain of the chart majorant of `M_{r_b}` applied to the transition
majorant is at most `P_ν ε^{95/22}e^{m₀/(2ν)}‖T‖_{L²_τL^{22/19}}` (kernel `ε^{46/11}`, receiver
factor `√ρ = ε^{3/22}e^{m₀/(2ν)}`). -/
def TransMajRepAt : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * (D.level n).ε * cOf (D.level n).ν)
          ((D.level n).ε⁻¹ * Real.sqrt (5 * (D.level n).ν / 6)) T →
        SepMoment (2 * (D.level n).ε * cOf (D.level n).ν) T → IsAxiSource T →
        htMaj (cOf (D.level n).ν) ((D.level n).ρb D.Pl D.K) (multMaj (D.level n).ε⁻¹
            (D.level n).rb (transMaj (D.level n).ν (D.level n).ε⁻¹ (IIIa.srcNorm T))) ≤
          ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (95 / 22 : ℝ) *
              Real.exp (D.K.m0 / 2 / (D.level n).ν)) *
            IIIa.ltauLq (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19) (IIIa.srcNorm T)

end SeqData

/-- (E1) The thin-receiver entry for every standing sequence (source 5323-5341). -/
def TransMajThin (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → D.TransMajThinAt

/-- (E2) The repair-receiver entry for every standing sequence (source 5323-5341). -/
def TransMajRep (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → D.TransMajRepAt

/-! ## 2. The kernel steps (generic) -/

/-- **The pointwise exponent `79/22` for the transition majorant** (source 3647 `sep:young`
pointwise with `p = 22/19`, `b = 22/3`: `D^{-4+3/b} = D^{-79/22}`; 5337-5338; 4181-4192 and
5339-5341: the outward primitive "has the same norm powers"): for `0 < ν ≤ 1`, `R ≥ 1`, `P > 0` and
every jointly measurable `P`-periodic `g ≥ 0` vanishing outside the old disk
`ϱ ≤ R√(5ν/6)`, at **every** receiver `y`,
`‖transMaj ν R g (·, y)‖_{L²_τ} ≤ C ν^{-k} R^{-79/22} ‖g‖_{L²_τL^{22/19}}`.
(Order-zero part: `IIIa.SepDomPointwise`, `j = 0`, `a = 0`, gap `D = R√ν(1-√(5/6))`; order-one
part: `j = 1`, `D^{-101/22}L⁻¹ ≤ C R^{-79/22}` for `R ≥ 1`; primitive part: Minkowski in `ρ`, the gap
`|(ρ,0,z) - λz'| ≥ ρ - r_o` for `g` supported in the old disk, `∫_L^∞ ρ(ρ - r_o)^{-79/22}dρ ≤
C L^{-35/22}`, times `L⁻²`.) -/
def TransMajPointL2 : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (ν R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P →
    ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
      (∀ τ (z : Space), R * Real.sqrt (5 * ν / 6) < ϱ z → g τ z = 0) →
        ∀ y : Space, IIIa.ltauAt P (fun τ => transMaj ν R g τ y) ≤
          ENNReal.ofReal (C * ν⁻¹ ^ k * R ^ (-(79 / 22 : ℝ))) * IIIa.ltauLq P (22 / 19) g

/-- **The `L^{11/3}` kernel for the transition majorant** (source 3631-3646 `sep:young` with
`p = 22/19`, `q = 22/3`, `b = 11/3`: `D^{-4+3/b} = D^{-35/11}`; 5338-5341; 4181-4192): for
`0 < ν ≤ 1`, `R ≥ 1`, `P > 0` and every jointly measurable `P`-periodic `g ≥ 0` vanishing outside the
old disk, `‖transMaj ν R g‖_{L²_τL^{22/3}} ≤ C ν^{-k} R^{-35/11} ‖g‖_{L²_τL^{22/19}}`.
(Order-zero and order-one parts: `IIIa.SepDomYoung`; primitive part: the `q = 22/3` analogue of
`OutMajAnnulusL2` (`VertYoungL2`, `AnnulusFubiniL2`), `‖1_ann outMaj‖_{L²_τL^{22/3}} ≤
C L^{-13/11}‖g‖`, times `L⁻²`.) -/
def TransMajL223 : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (ν R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P →
    ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
      (∀ τ (z : Space), R * Real.sqrt (5 * ν / 6) < ϱ z → g τ z = 0) →
        IIIa.ltauLq P (22 / 3) (transMaj ν R g) ≤
          ENNReal.ofReal (C * ν⁻¹ ^ k * R ^ (-(35 / 11 : ℝ))) * IIIa.ltauLq P (22 / 19) g

/-! ## 3. The multiplication steps (along the sequence) -/

namespace SeqData

variable (D : SeqData)

/-- **Thin multiplication on the transition window** (source 2697, 2706, 2717-2723: `Z₁` with
weight `W² s^{-1/2}`, `V_m(s) = ‖W v(s)‖_{L²_ηL^∞_q} ≤ P_ν((1+s)^{-3/4} + ε(1+s)^{-1/4})`,
`IIIa.StressCoefficients`, fourth clause; 2666-2668: `τ = 2q/R + log s`, so a `q`-cell of length `c`
is one phase period `P = 2c/R`; 5337-5338 "followed by `ρR`" is the next step): for large `n` and
every measurable, `2εc`-periodic, axisymmetric `f ≥ 0` vanishing off the transition annulus whose
phase norm is at most `A` at every receiver,
`‖multMaj R V f‖_{Z₁} ≤ C ν^{-k} A` (the window is `4/(5ν) ≤ s ≤ 1/ν`;
`∫_q f² dq = c‖f(y,·)‖²_{L²_τ}`, Hölder in `η` with `V_m(s)`, `∫ s^{-3/2}V_m(s)² ds` over the window). -/
def ThinChartAt : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ (f : ℝ → Space → ℝ≥0∞) (A : ℝ≥0∞),
      ChartGood (2 * (D.level n).ε * cOf (D.level n).ν) f →
      (∀ τ (y : Space), y ∉ streamAnn (D.level n).ν (D.level n).ε⁻¹ → f τ y = 0) →
      (∀ y : Space, IIIa.ltauAt (2 * (D.level n).ε * cOf (D.level n).ν) (fun τ => f τ y) ≤ A) →
        z1Maj (cOf (D.level n).ν) D.K.mZ (multMaj (D.level n).ε⁻¹ (D.level n).V f) ≤
          ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k) * A

/-- **Repair multiplication on the transition window** (source 5134-5139:
`‖r_b‖_{C_τL^{11/4}} ≤ P_νρ`, `ρ = ε^{3/11}e^{m₀/ν}`; 2698-2713: `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}`;
2683-2689: chart-to-physical `2πr dr dz = πR²s^{-5/2}ds dη`, `c⁻¹dq = dτ/P`; 5338-5339: Hölder
`1/2 = 4/11 + 3/22` against the `L^{22/3}` receiver of the `L^{11/3}` kernel): for large `n` and
every measurable, `2εc`-periodic, axisymmetric `f ≥ 0` vanishing off the transition annulus,
`‖multMaj R r_b f‖_{ρ_b^{-1/2}H_T} ≤ C ν^{-k} ε^{25/22}e^{m₀/(2ν)} ‖f‖_{L²_τL^{22/3}}`
(`ρ_b^{-1/2}·R⁻¹·P_νρ`). -/
def RepChartAt : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ f : ℝ → Space → ℝ≥0∞,
      ChartGood (2 * (D.level n).ε * cOf (D.level n).ν) f →
      (∀ τ (y : Space), y ∉ streamAnn (D.level n).ν (D.level n).ε⁻¹ → f τ y = 0) →
        htMaj (cOf (D.level n).ν) ((D.level n).ρb D.Pl D.K)
            (multMaj (D.level n).ε⁻¹ (D.level n).rb f) ≤
          ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (25 / 22 : ℝ) *
              Real.exp (D.K.m0 / 2 / (D.level n).ν)) *
            IIIa.ltauLq (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 3) f

end SeqData

/-- (M1) Thin multiplication for every standing sequence. -/
def ThinChart (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → D.ThinChartAt

/-- (M2) Repair multiplication for every standing sequence. -/
def RepChart (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → D.RepChartAt

/-! ## 4. Compositions (proved) -/

/-- The source norm of a separated source is measurable, periodic and vanishes off the old
disk. -/
theorem tt_srcNorm_facts {P rOut : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P rOut T) :
    Measurable (Function.uncurry (IIIa.srcNorm T)) ∧
      (∀ τ z, IIIa.srcNorm T (τ + P) z = IIIa.srcNorm T τ z) ∧
      ∀ τ (z : Space), rOut < ϱ z → IIIa.srcNorm T τ z = 0 := by
  refine ⟨?_, fun τ z => by simp only [IIIa.srcNorm, hT.periodic], fun τ z hz => ?_⟩
  · have e : Function.uncurry (IIIa.srcNorm T) = fun p : ℝ × Space =>
        ENNReal.ofReal (Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, T p.1 p.2 i j ^ 2)) := rfl
    rw [e]
    exact ENNReal.measurable_ofReal.comp (Measurable.sqrt (Finset.measurable_sum _
      fun i _ => Finset.measurable_sum _ fun j _ => (hT.measurable i j).pow_const 2))
  · have h0 : T τ z = 0 := hT.support τ z hz
    simp [IIIa.srcNorm, IIIa.tensorNorm, h0]

theorem tt_chartGood_add {P : ℝ} {F G : ℝ → Space → ℝ≥0∞} (hF : ChartGood P F)
    (hG : ChartGood P G) : ChartGood P (fun τ y => F τ y + G τ y) := by
  refine ⟨hF.1.add hG.1, fun τ y => ?_, fun τ y y' h1 h2 => ?_⟩
  · show F (τ + P) y + G (τ + P) y = F τ y + G τ y
    rw [hF.2.1, hG.2.1]
  · show F τ y' + G τ y' = F τ y + G τ y
    rw [hF.2.2 τ y y' h1 h2, hG.2.2 τ y y' h1 h2]

/-- The transition majorant of a separated axisymmetric source is measurable, periodic,
axisymmetric (`TransMajFacts`) and vanishes off the annulus. -/
theorem tt_transMaj_good (hF : TransMajFacts) {ν R P : ℝ} (hν : 0 < ν) (hR : 0 < R) (hP : 0 < P)
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hA : IsAxiSource T) :
    ChartGood P (transMaj ν R (IIIa.srcNorm T)) ∧
      ∀ τ (y : Space), y ∉ streamAnn ν R → transMaj ν R (IIIa.srcNorm T) τ y = 0 := by
  obtain ⟨h1, h2, h3⟩ := hF ν R P hν hR hP T hT hA
  refine ⟨tt_chartGood_add (tt_chartGood_add h1 h2) h3, fun τ y hy => ?_⟩
  simp [transMaj, transMajW, transMajD, transMajS, Set.indicator, hy]

/-- `(ε⁻¹)^{-a} = ε^a`. -/
theorem tt_inv_rpow_neg {ε : ℝ} (hε : 0 < ε) (a : ℝ) : ε⁻¹ ^ (-a) = ε ^ a := by
  rw [Real.inv_rpow hε.le, Real.rpow_neg hε.le, inv_inv]

namespace SeqData

variable (D : SeqData)

/-- **The thin entry** from the pointwise exponent and the thin multiplication (source 5337-5338,
2717-2723). -/
theorem transMajThinAt_of {dm dp : ℝ} (hst : D.RepairStanding dm dp) (hF : TransMajFacts)
    (hP : TransMajPointL2) (hC : D.ThinChartAt) : D.TransMajThinAt := by
  obtain ⟨C1, k1, hC1, hP'⟩ := hP
  obtain ⟨C2, k2, hC2, hev⟩ := hC
  refine ⟨C2 * C1, k2 + k1, mul_nonneg hC2 hC1, ?_⟩
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hev, hev2] with n hn e2 T hTS hTM hTA
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 hε
  have hR1 : 1 ≤ (D.level n).ε⁻¹ := (one_le_inv₀ hε).2 e2.2
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν
  have hPp : 0 < 2 * (D.level n).ε * cOf (D.level n).ν := by positivity
  obtain ⟨hG, hvan⟩ := tt_transMaj_good hF hν hR hPp hTS hTA
  obtain ⟨g1, g2, g3⟩ := tt_srcNorm_facts hTS
  have hpt := hP' (D.level n).ν (D.level n).ε⁻¹ _ hν e2.1 hR1 hPp (IIIa.srcNorm T) g1 g2 g3
  refine (hn _ _ hG hvan hpt).trans_eq ?_
  rw [tt_inv_rpow_neg hε, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [pow_add]
  ring

/-- **The repair entry** from the `L^{11/3}` kernel and the repair multiplication (source
5338-5341, 5134-5139): `ε^{25/22}·ε^{35/11} = ε^{95/22}`. -/
theorem transMajRepAt_of {dm dp : ℝ} (hst : D.RepairStanding dm dp) (hF : TransMajFacts)
    (hK : TransMajL223) (hC : D.RepChartAt) : D.TransMajRepAt := by
  obtain ⟨C1, k1, hC1, hK'⟩ := hK
  obtain ⟨C2, k2, hC2, hev⟩ := hC
  refine ⟨C2 * C1, k2 + k1, mul_nonneg hC2 hC1, ?_⟩
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hev, hev2] with n hn e2 T hTS hTM hTA
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 hε
  have hR1 : 1 ≤ (D.level n).ε⁻¹ := (one_le_inv₀ hε).2 e2.2
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν
  have hPp : 0 < 2 * (D.level n).ε * cOf (D.level n).ν := by positivity
  obtain ⟨hG, hvan⟩ := tt_transMaj_good hF hν hR hPp hTS hTA
  obtain ⟨g1, g2, g3⟩ := tt_srcNorm_facts hTS
  have hk := hK' (D.level n).ν (D.level n).ε⁻¹ _ hν e2.1 hR1 hPp (IIIa.srcNorm T) g1 g2 g3
  refine (hn _ hG hvan).trans ((mul_le_mul_right hk _).trans_eq ?_)
  rw [tt_inv_rpow_neg hε, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have e : (D.level n).ε ^ (95 / 22 : ℝ) =
      (D.level n).ε ^ (25 / 22 : ℝ) * (D.level n).ε ^ (35 / 11 : ℝ) := by
    rw [← Real.rpow_add hε]; norm_num
  rw [e, pow_add]
  ring

end SeqData

/-- **`TransMajThin`** from its two steps. -/
theorem transMajThin_of {dm dp : ℝ} (hF : TransMajFacts) (hP : TransMajPointL2)
    (hC : ThinChart dm dp) : TransMajThin dm dp :=
  fun D hst => D.transMajThinAt_of hst hF hP (hC D hst)

/-- **`TransMajRep`** from its two steps. -/
theorem transMajRep_of {dm dp : ℝ} (hF : TransMajFacts) (hK : TransMajL223)
    (hC : RepChart dm dp) : TransMajRep dm dp :=
  fun D hst => D.transMajRepAt_of hst hF hK (hC D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
