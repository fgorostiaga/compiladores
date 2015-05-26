structure tigertips =
struct

datatype R = RO | RW

type unique = unit ref

datatype Tipo = TUnit
	| TNil
	| TInt of R
	| TString
	| TArray of Tipo * unique
	| TRecord of (string * Tipo * int) list * unique
	| TFunc of Tipo list * Tipo
	| TTipo of string * Tipo option ref

end
