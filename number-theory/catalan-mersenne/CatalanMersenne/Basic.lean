import CatalanMersenne.Defs

namespace CatalanMersenne

theorem catalanMersenne_zero : catalanMersenne 0 = 2 := rfl

theorem catalanMersenne_one : catalanMersenne 1 = 3 := by
  decide

theorem catalanMersenne_two : catalanMersenne 2 = 7 := by
  decide

theorem catalanMersenne_three : catalanMersenne 3 = 127 := by
  decide

theorem isCatalanMersennePrime_zero : IsCatalanMersennePrime 0 := by
  decide

theorem isCatalanMersennePrime_one : IsCatalanMersennePrime 1 := by
  decide

theorem isCatalanMersennePrime_two : IsCatalanMersennePrime 2 := by
  decide

theorem isCatalanMersennePrime_three : IsCatalanMersennePrime 3 := by
  decide

end CatalanMersenne
