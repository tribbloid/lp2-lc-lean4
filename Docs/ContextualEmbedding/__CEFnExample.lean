import «ContextualEmbedding».CE

namespace ContextualEmbedding.CE

open STLCCtx

def binaryReturnsFirst : STLCCtx ts (a :-> b :-> a) :=
  CLam (λ x => CLam (λ _y => CVar x))

#check binaryReturnsFirst

end ContextualEmbedding.CE
