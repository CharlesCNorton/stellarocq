"""Which coefficients of a VMEC pressure profile carry its amplitude.

VMEC multiplies every profile by PRES_SCALE and does not write that number to
the wout, so the coefficients a wout carries describe the input profile and
not the pressure the equilibrium balances. The generator puts the scale back
into the coefficients that are linear in it; every other coefficient of a
family is an exponent, a position, a width or a mixing fraction and has to be
the file's own exactly.

Both gen/make_cert.py, which applies the scale, and gen/verify_cert.py, which
reads the coefficients back against the wout, need to agree on which slots
those are. They each had their own copy, and a copy that drifted would let the
guard accept a certificate whose pressure is not the one the equilibrium
balances: the guard would take a scaled coefficient for an unscaled one and
compare it against `am` rather than reading the pressure back against `pres`.

This is a table of facts about VMEC's profile families, not a piece of the
certificate reader, so sharing it costs the guard none of the independence it
exists for: gen/verify_cert.py still parses the file and evaluates the
pressure with its own code.
"""

# Slot indices of the am block that scale with PRES_SCALE, per closed form.
AMPLITUDE_SLOTS = {
    "POWER": frozenset(range(21)),
    "TWOPOWER": frozenset({0}),
    "TWOPOWERGS": frozenset({0}),
    "GAUSSTRUNC": frozenset({0}),
    "TWOLORENTZ": frozenset({0}),
    "PEDESTAL": frozenset(set(range(16)) | {17}),
    "RATIONAL": frozenset(range(10)),
}
