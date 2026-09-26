import MS.Main

open MeasureTheory

namespace MS

/-- Overlap conditions on the buyer/seller type intervals: each interval is
nontrivial and the two supports overlap in both directions. -/
def Overlap (a1 b1 a2 b2 : ℝ) : Prop :=
  a1 < b1 ∧ a2 < b2 ∧ a2 < b1 ∧ a1 < b2

/-- The full Myerson-Satterthwaite model: type intervals, atomless full-support
probability measures with positive densities, allocation and transfer rules,
ex post efficiency, Bayesian incentive compatibility, interim individual
rationality, and weak (ex ante) budget balance. -/
def IsModel (a1 b1 a2 b2 : ℝ) (mu nu : Measure ℝ)
    (q tb tc : ℝ × ℝ → ℝ) : Prop :=
  Overlap a1 b1 a2 b2 ∧
  IsProbabilityMeasure mu ∧
  IsProbabilityMeasure nu ∧
  MeasureTheory.NullSingletonClass mu ∧
  MeasureTheory.NullSingletonClass nu ∧
  Measure.support mu ⊆ Set.Icc a1 b1 ∧
  Measure.support nu ⊆ Set.Icc a2 b2 ∧
  Measure.AbsolutelyContinuous (volume.restrict (Set.Icc a1 b1)) mu ∧
  Measure.AbsolutelyContinuous (volume.restrict (Set.Icc a2 b2)) nu ∧
  (∀ s : Set ℝ, IsOpen s → (s ∩ Set.Ioo a1 b1).Nonempty → 0 < mu s) ∧
  (∀ s : Set ℝ, IsOpen s → (s ∩ Set.Ioo a2 b2).Nonempty → 0 < nu s) ∧
  AEStronglyMeasurable q (mu.prod nu) ∧
  (∀ v ∈ Set.Icc a1 b1, AEStronglyMeasurable (fun c => q (v, c)) nu) ∧
  (∀ c ∈ Set.Icc a2 b2, AEStronglyMeasurable (fun v => q (v, c)) mu) ∧
  (∀ v ∈ Set.Icc a1 b1, ∀ c ∈ Set.Icc a2 b2, 0 ≤ q (v, c)) ∧
  (∀ v ∈ Set.Icc a1 b1, ∀ c ∈ Set.Icc a2 b2, q (v, c) ≤ 1) ∧
  Integrable tb (mu.prod nu) ∧
  Integrable tc (mu.prod nu) ∧
  (∀ v ∈ Set.Icc a1 b1, Integrable (fun c => tb (v, c)) nu) ∧
  (∀ c ∈ Set.Icc a2 b2, Integrable (fun v => tc (v, c)) mu) ∧
  q =ᵐ[(mu.prod nu).restrict {p | p.2 < p.1}] (fun _ => (1 : ℝ)) ∧
  q =ᵐ[(mu.prod nu).restrict {p | p.1 < p.2}] (fun _ => (0 : ℝ)) ∧
  (∀ v ∈ Set.Icc a1 b1, ∀ v' ∈ Set.Icc a1 b1,
    interimU q tb nu v ≥ interimU q tb nu v' + (v - v') * interimQ q nu v') ∧
  (∀ c ∈ Set.Icc a2 b2, ∀ c' ∈ Set.Icc a2 b2,
    interimW q tc mu c ≥ interimW q tc mu c' + (c' - c) * interimR q mu c') ∧
  (∀ v ∈ Set.Icc a1 b1, 0 ≤ interimU q tb nu v) ∧
  (∀ c ∈ Set.Icc a2 b2, 0 ≤ interimW q tc mu c) ∧
  (∫ p, tc p ∂(mu.prod nu)) ≤ (∫ p, tb p ∂(mu.prod nu))

end MS

namespace MS.Palomar

/-- Myerson-Satterthwaite impossibility (continuous version): no allocation and transfer rules can simultaneously satisfy ex post efficiency, Bayesian incentive compatibility, interim individual rationality, and (weak/ex ante) budget balance when the buyer and seller type supports overlap. -/
theorem myersonSatterthwaite (a1 b1 a2 b2 : ℝ) (mu nu : Measure ℝ)
    (q tb tc : ℝ × ℝ → ℝ) (h : MS.IsModel a1 b1 a2 b2 mu nu q tb tc) : False := by
  obtain ⟨hov, hmu, hnu, hmu_atom, hnu_atom, hmu_supp, hnu_supp, hvolB, hvolS,
    hfullB, hfullS, hq_meas, hq_secB, hq_secS, hq_nn, hq_le,
    htb_int, htc_int, htb_sec, htc_sec, heffB, heffS, hbicB, hbicS, hirB, hirS, hbb⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := hov
  exact MSData.MS_impossible
    { a1 := a1, b1 := b1, a2 := a2, b2 := b2,
      h1 := h1, h2 := h2, h3 := h3, h4 := h4,
      mu := mu, nu := nu, mu_probability := hmu, nu_probability := hnu,
      mu_noAtoms := hmu_atom, nu_noAtoms := hnu_atom,
      mu_supported := hmu_supp, nu_supported := hnu_supp,
      vol_absB := hvolB, vol_absS := hvolS,
      mu_fullSupport := hfullB, nu_fullSupport := hfullS,
      q := q, q_measurable := hq_meas, q_sectionB := hq_secB, q_sectionS := hq_secS,
      q_nonneg := hq_nn, q_le_one := hq_le,
      tb := tb, tc := tc, tb_integrable := htb_int, tc_integrable := htc_int,
      tb_section := htb_sec, tc_section := htc_sec,
      effB := heffB, effS := heffS, bicB := hbicB, bicS := hbicS,
      irB := hirB, irS := hirS, bb := hbb }

end MS.Palomar
