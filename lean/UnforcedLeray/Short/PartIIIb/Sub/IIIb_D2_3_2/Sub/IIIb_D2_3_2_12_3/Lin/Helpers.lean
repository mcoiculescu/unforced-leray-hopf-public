import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.MeasureCmp
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.ChartBound
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE

/-!
# Helpers for `StrPairLin`, `StrPairBd`, `StrPairContNonpos` (`PartIII-b:IIIb-D2/3/2/12/3`)

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 4284-4286.

Pointwise linearity of `strPhys`, linearity of the iterated `stressPair` integral when the
integrands are integrable on the phase cell, finite region norms of `strSum T` from
`StrMeasureCmp`, and the a.e. behaviour of `strSum` on sums and scalar multiples.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

theorem nsSym_add_lin (T T' : Ten3) :
    NearInst.nsSym (T + T') = NearInst.nsSym T + NearInst.nsSym T' := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [NearInst.nsSym, NearInst.symRZ] <;> ring

theorem nsSym_smul_lin (k : ℝ) (T : Ten3) :
    NearInst.nsSym (k • T) = k • NearInst.nsSym T := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [NearInst.nsSym, NearInst.symRZ] <;> ring

theorem strPhys_add_lin (R c : ℝ) (g g' : Chart → Ten3) :
    strPhys R c (g + g') = strPhys R c g + strPhys R c g' := by
  funext x
  simp only [strPhys, NearInst.cartLift, Pi.add_apply, nsSym_add_lin, smul_add, Matrix.mul_add,
    Matrix.add_mul]

theorem strPhys_smul_lin (R c k : ℝ) (g : Chart → Ten3) :
    strPhys R c (k • g) = fun x => k • strPhys R c g x := by
  funext x
  simp only [strPhys, NearInst.cartLift, Pi.smul_apply, nsSym_smul_lin]
  rw [smul_comm, Matrix.mul_smul, Matrix.smul_mul]

theorem integrand_add_lin (Tp Tp' : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ) (Φ : ℝ × Space → CVec3)
    (x : ℝ × Space) :
    (∑ i : Fin 3, ∑ j : Fin 3, (((Tp + Tp') x i j : ℝ) : ℂ) * dy j Φ x i) =
      (∑ i : Fin 3, ∑ j : Fin 3, ((Tp x i j : ℝ) : ℂ) * dy j Φ x i) +
        (∑ i : Fin 3, ∑ j : Fin 3, ((Tp' x i j : ℝ) : ℂ) * dy j Φ x i) := by
  simp only [Pi.add_apply, Matrix.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]

/-- The iterated phase integral equals the integral over the restricted cell when the integrand is
integrable there (Fubini on `Ioc 0 P × univ`, as in `pairF_eq_restrictedProductIntegral`). -/
theorem phaseInt_eq_cell_lin (P : ℝ) (f : ℝ × Space → ℂ)
    (hf : Integrable f (volume.restrict (phaseCell P))) :
    phaseInt P f = P⁻¹ • ∫ z, f z ∂(volume.restrict (phaseCell P)) := by
  let μ : Measure ℝ := volume
  let ν : Measure Space := volume
  have hprod : (volume : Measure (ℝ × Space)).restrict (phaseCell P) =
      (μ.restrict (Ioc (0 : ℝ) P)).prod ν := by
    simpa [μ, ν, phaseCell, Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space)) (Ioc (0 : ℝ) P)).symm
  have hInt' : Integrable f ((μ.restrict (Ioc (0 : ℝ) P)).prod ν) := by
    rw [← hprod]
    exact hf
  have hiter : ∫ t in Ioc (0 : ℝ) P, ∫ y : Space, f (t, y) =
      ∫ z, f z ∂(volume.restrict (phaseCell P)) := by
    calc
      ∫ t in Ioc (0 : ℝ) P, ∫ y : Space, f (t, y) =
          ∫ t, ∫ y, f (t, y) ∂ν ∂(μ.restrict (Ioc 0 P)) := by
            rfl
      _ = ∫ z, f z ∂((μ.restrict (Ioc 0 P)).prod ν) :=
        (integral_prod _ hInt').symm
      _ = ∫ z, f z ∂(volume.restrict (phaseCell P)) := by
        rw [hprod]
  unfold phaseInt
  rw [hiter]

/-- Additivity of the stress pairing when both integrands are integrable on the phase cell. -/
theorem stressPair_add_lin {P : ℝ} {Tp Tp' : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ}
    {Φ : ℝ × Space → CVec3}
    (h1 : Integrable (fun x : ℝ × Space =>
      ∑ i : Fin 3, ∑ j : Fin 3, ((Tp x i j : ℝ) : ℂ) * dy j Φ x i) (volume.restrict (phaseCell P)))
    (h2 : Integrable (fun x : ℝ × Space =>
      ∑ i : Fin 3, ∑ j : Fin 3, ((Tp' x i j : ℝ) : ℂ) * dy j Φ x i) (volume.restrict (phaseCell P))) :
    stressPair P (Tp + Tp') Φ = stressPair P Tp Φ + stressPair P Tp' Φ := by
  unfold stressPair
  have hfun : (fun x : ℝ × Space =>
      ∑ i : Fin 3, ∑ j : Fin 3, (((Tp + Tp') x i j : ℝ) : ℂ) * dy j Φ x i) =
      fun x => (∑ i : Fin 3, ∑ j : Fin 3, ((Tp x i j : ℝ) : ℂ) * dy j Φ x i) +
        (∑ i : Fin 3, ∑ j : Fin 3, ((Tp' x i j : ℝ) : ℂ) * dy j Φ x i) :=
    funext (integrand_add_lin Tp Tp' Φ)
  have hsum : Integrable (fun x : ℝ × Space =>
      (∑ i : Fin 3, ∑ j : Fin 3, ((Tp x i j : ℝ) : ℂ) * dy j Φ x i) +
        (∑ i : Fin 3, ∑ j : Fin 3, ((Tp' x i j : ℝ) : ℂ) * dy j Φ x i))
      (volume.restrict (phaseCell P)) := h1.add h2
  rw [hfun, phaseInt_eq_cell_lin P _ hsum, phaseInt_eq_cell_lin P _ h1,
    phaseInt_eq_cell_lin P _ h2, integral_add h1 h2, smul_add]

/-- Real homogeneity of the stress pairing (no integrability needed). -/
theorem stressPair_smul_lin (P k : ℝ) (Tp : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ : ℝ × Space → CVec3) :
    stressPair P (fun x => k • Tp x) Φ = k • stressPair P Tp Φ := by
  unfold stressPair
  beta_reduce
  have hpt : ∀ x : ℝ × Space,
      (∑ i : Fin 3, ∑ j : Fin 3, (((k • Tp x) i j : ℝ) : ℂ) * dy j Φ x i) =
        (k : ℂ) * ∑ i : Fin 3, ∑ j : Fin 3, ((Tp x i j : ℝ) : ℂ) * dy j Φ x i := by
    intro x
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hfun : (fun x : ℝ × Space =>
      ∑ i : Fin 3, ∑ j : Fin 3, (((k • Tp x) i j : ℝ) : ℂ) * dy j Φ x i) =
      fun x => (k : ℂ) * ∑ i : Fin 3, ∑ j : Fin 3, ((Tp x i j : ℝ) : ℂ) * dy j Φ x i :=
    funext hpt
  rw [hfun]
  unfold phaseInt
  simp only [integral_const_mul, Complex.real_smul]
  ring

theorem strG_norm_lin {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) :
    ‖T‖ = ‖T.fst‖ + ‖T.snd‖ := by
  rw [WithLp.prod_norm_eq_add (by norm_num)]
  simp

theorem lintegral_rpow_two_lt_top_lin {E : Type*} [NormedAddCommGroup E] {f : Chart → E}
    {μ : Measure Chart} (hf : MemLp f 2 μ) : (∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂μ) < ⊤ := by
  have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num)
    (by norm_num)).1 hf.eLpNorm_lt_top
  simpa [ENNReal.toReal_ofNat] using h

theorem strSum_measurable_lin {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) :
    Measurable (strSum T) :=
  (Lp.stronglyMeasurable T.fst).measurable.add (Lp.stronglyMeasurable T.snd).measurable

/-- The region `StrRegion Y` has finite second-moment norm for `strSum T` (both gain components
dominate `ageμ c (-1/2)` on the region by `StrMeasureCmp`). -/
theorem memLp_region_strSum_lin {c mZ ρb γ ν : ℝ} (hν : 0 < ν) (hρ : 0 < ρb) (Y : ℝ)
    (T : StrG c mZ ρb γ ν) :
    MemLp (strSum T) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) := by
  obtain ⟨K, hK, -, h1, h2, -⟩ := strMeasureCmp_proved c mZ ρb γ ν hν hρ Y
  have hf1 : MemLp (T.fst : Chart → Ten3) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) :=
    MemLp.of_measure_le_smul hK h1 ((Lp.memLp T.fst).restrict (StrRegion Y))
  have hf2 : MemLp (T.snd : Chart → Ten3) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) :=
    (MemLp.of_measure_le_smul hK h2 (Lp.memLp T.snd)).restrict (StrRegion Y)
  exact hf1.add hf2

/-- The `Z₁` part alone has finite region norm (uses `StrMeasureCmp` at `ρ_b = 1`, which does not
involve `ρ_b` in the `Z₁` clause). -/
theorem memLp_region_z1_lin {c mZ γ ν : ℝ} (hν : 0 < ν) (Y : ℝ)
    (f : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) :
    MemLp (f : Chart → Ten3) 2 ((ageμ c (-1 / 2)).restrict (StrRegion Y)) := by
  obtain ⟨K, hK, -, h1, -, -⟩ := strMeasureCmp_proved c mZ 1 γ ν hν one_pos Y
  exact MemLp.of_measure_le_smul hK h1 ((Lp.memLp f).restrict (StrRegion Y))

theorem strSum_add_ae_lin {c mZ ρb γ ν : ℝ} (hν : 0 < ν) (hρ : 0 < ρb) (T T' : StrG c mZ ρb γ ν) :
    strSum (T + T') =ᵐ[ageμ c (-1 / 2)] strSum T + strSum T' := by
  obtain ⟨K, hK, -, h1, h2, h3⟩ := strMeasureCmp_proved c mZ ρb γ ν hν hρ 0
  have hac1 : ageμ c (-1 / 2) ≪ gainZ1Measure c mZ γ ν := h3
  have hac2 : ageμ c (-1 / 2) ≪ gainHTMeasure c ρb γ ν := Measure.absolutelyContinuous_of_le_smul h2
  filter_upwards [hac1.ae_le (Lp.coeFn_add T.fst T'.fst),
    hac2.ae_le (Lp.coeFn_add T.snd T'.snd)] with p hp1 hp2
  have e1 : (T + T').fst p = T.fst p + T'.fst p := hp1
  have e2 : (T + T').snd p = T.snd p + T'.snd p := hp2
  simp only [strSum, Pi.add_apply]
  rw [e1, e2]
  abel

theorem strSum_smul_ae_lin {c mZ ρb γ ν : ℝ} (hν : 0 < ν) (hρ : 0 < ρb) (k : ℝ)
    (T : StrG c mZ ρb γ ν) :
    strSum (k • T) =ᵐ[ageμ c (-1 / 2)] k • strSum T := by
  obtain ⟨K, hK, -, h1, h2, h3⟩ := strMeasureCmp_proved c mZ ρb γ ν hν hρ 0
  have hac1 : ageμ c (-1 / 2) ≪ gainZ1Measure c mZ γ ν := h3
  have hac2 : ageμ c (-1 / 2) ≪ gainHTMeasure c ρb γ ν := Measure.absolutelyContinuous_of_le_smul h2
  filter_upwards [hac1.ae_le (Lp.coeFn_smul k T.fst),
    hac2.ae_le (Lp.coeFn_smul k T.snd)] with p hp1 hp2
  have e1 : (k • T).fst p = k • T.fst p := hp1
  have e2 : (k • T).snd p = k • T.snd p := hp2
  simp only [strSum, Pi.smul_apply]
  rw [e1, e2, smul_add]

end UnforcedLeray.Short.PartIIIb.Concrete
