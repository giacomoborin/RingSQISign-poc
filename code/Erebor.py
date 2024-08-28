# Python imports
from hashlib import shake_128

# SageMath imports
from sage.all import proof # type: ignore

# Local imports
from .setup import p
from .isogenies import EllipticCurveIsogenyFactored

proof.all(False)

from .SQISign import ( 
    specialSQISign, specialSQISign_strong, simulation, 
    ker_for_challenge, curve_to_int
    )



class Erebor():
    def __init__(self, ring, user:specialSQISign, full_anon = False):
        """
        The object need to contatin the ring of public keys

        We only use the object to store intermediate values,
        we could also init this with parameters and stop using
        globals.
        """
        # Keys
        self.ring = ring
        if not all([E.order() == (p**2-1)**2 for E in self.ring]):
            raise ValueError('Publick Keys need to be supersingular elliptic curves')

        if user:
            if not user.export_public_key() in self.ring:
                raise ValueError('The user key need to be in the ring')
            self.user = user
            self.usr_idx = self.ring.index(user.export_public_key())
            self.e = user.e

        self.full_anon = full_anon
        self.ring_hash = sum([curve_to_int(E) for E in self.ring])

    def export_ring(self):
        """
        Helper function to return the public key

        TODO: this could be compressed, probably.
        """
        return self.ring
        
    def challenge_from_message_ring(self, Epk, Ecmt, mes):
        h = shake_128(mes).digest(128)
        salt = int.from_bytes(h, "big") 
        salt += self.ring_hash
        salt += curve_to_int(Ecmt)
        return ker_for_challenge(Epk, salt=salt)

    def sign(self, msg):
        """
        Use SQISign to sign a message by creating a challenge
        isogeny from the message and generating a response S
        from the challenge.
        Input: msg: the message to be signed
        Output: sig: a signature tuple (ker, list)
                ker : the kernel of the challenge
                list: contains N bitstrings associated to isogenies
        """
        N = len(self.ring)
        Ecmt = self.user.commitment()
        idx_start = (self.usr_idx + 1) % N
        phi_ker = self.challenge_from_message_ring(self.ring[idx_start], Ecmt, mes=msg)
        commitments = [Ecmt for _ in range(N)]
        challenges = [phi_ker for _ in range(N)]
        responses = ['' for _ in range(N)]
        for idx in range(idx_start,idx_start + N - 1):
            i = idx % N
            Epki = challenges[i].curve()
            phi = EllipticCurveIsogenyFactored(Epki, challenges[i])
            Echi = phi.codomain()
            responses[i], commitments[i] = simulation(Estart=Echi, length=self.e)
            challenges[(i+1) % N] = self.challenge_from_message_ring(self.ring[(i+1) % N], commitments[i], mes=msg)
        S = self.user.response(challenges[self.usr_idx])
        responses[self.usr_idx] = S
        return (challenges[0], responses)

    def verify(self, sig, msg):
        """
        Wrapper for verify a ring signature

        Input: 
               sig: a signature tuple (ker, list)
                   ker: a kernel from an isogeny
                   S: a compressed bitstring of the response isogeny EA → E2
               msg: the message which has been signed
        Output: True if the signature is valid, False otherwise
        """
        # Extract pieces from signature
        N = len(self.ring)
        ker, responses = sig
        if self.full_anon:
            verifier = specialSQISign_strong()
        else:
            verifier = specialSQISign()
        
        keri = ker
        for i in range(N):
            valid, Ecmt = verifier._verify_deg_cyclic(
                Epk = self.ring[i], S = responses[i], ϕ_ker = keri
            )
            if not valid:
                return False
            keri = self.challenge_from_message_ring(
                Epk = self.ring[(i+1)%N], Ecmt=Ecmt, mes = msg
                )
        return keri == ker

