"""
Example of SQISign as a one-round interactive identification
protocol.

We imagine two parties, `prover` and `verifier`. The `prover`
demonstrates knowledge of the endomorphism ring End(EA) in the 
following way:

- The prover's public key is an elliptic curve EA, and their secret
is the isogeny E0 → EA, where End(E0) is known to everyone.

- The prover then makes a commitment by computing a second secret 
isogeny ψ : E0 → E1 and sends the codomain to the verifier.

- The verifier makes a challenge ϕ: E1 → E2 and sends ϕ to the prover

- The prover responds with σ : EA → E2, which is done via knowledge 
of End(EA) (through knowing End(E0) and τ : E0 → EA). The prover
sends σ to the verifier. 

- If ϕ_dual ∘ σ : EA → E1 is a cyclic isogeny, the verifier returns
true and false otherwise
"""

# Python imports
import time

# Local imports
from SQISign import SQISign
from utilities import print_info

# SQISign is a protocol between a prover and verifier
prover = SQISign()
verifier = SQISign()

print_info("Starting SQISign")
sqisign_time = time.time()

# The prover generates their keypair and makes a commitment
# which is a secret isogeny ψ : E0 → E1 and sends the codomain
# of ψ to the verifier
print_info("Computing Keypair")
prover.keygen()
EA = prover.export_public_key()

print_info("Computing Commitment")
E1 = prover.commitment()

# The verifier receives the commitment and makes a random
# challenge. Rather than sending the isogeny, the verifier
# simply sends the generator of the isogeny ϕ : E1 → E2
print_info("Computing Challenge")
phi_ker = verifier.challenge(E1)

# The verifier makes a response to the challenge, which is
# an isogeny σ : EA → E2 of degree l^e. The prover compresses
# σ to a bitstring S and sends this to the verifier
print_info("Computing Response")
S = prover.response(phi_ker)

# The verifier uses the prover's public key and their response
# S and checks if σ is an isogeny EA → E2 of degree l^e and
# whether ϕ_dual ∘ σ : EA → E1 is cyclic
print_info("Validating response")
valid = verifier.verify_response(EA, E1, S, phi_ker)

print_info(f"SQISign example worked: {valid}")
print_info(f"SQISign took {time.time() - sqisign_time:5f}")

from setup import p, T, Dc, l, f_step_max, e

print_info(f"Starting Recovering ideal from Isogeny")
isogeny_to_ideal_time = time.time()

from isogenies import EllipticCurveIsogenyFactored
from ideals import left_isomorphism
from compression import decompression

phi = EllipticCurveIsogenyFactored(E1, phi_ker, order=Dc)
E2 = phi.codomain()
E2.set_order((p**2 - 1) ** 2)

# Decompress sigma
print(f"INFO [TEST]: Decompressing the isogeny from a bitstring")

EA = prover.pk
sigma = decompression(EA, E2, S, l, f_step_max, e)
tau_prime, Itau, Jtau = prover.sk

from deuring import isogeny_to_ideal

# TODO : since the compressed isogeny already contain the kernel coordinates we 
# should try to use it to get immediatly the kernels.
J = isogeny_to_ideal(sigma,Jtau,tau_prime)
print(f'calculation took {time.time() - isogeny_to_ideal_time:5f}')

alpha = left_isomorphism(Itau, Jtau)
JJ = alpha  * J * (alpha** (-1))

from attack import distinguisher

print_info('Starting distinguisher')

dist_time = time.time()
distinguisher(JJ, Itau)
print(f'calculation took {time.time() - dist_time:5f}')





