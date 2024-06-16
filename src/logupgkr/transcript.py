from src.common_util.curve import Scalar
from src.common_util.merlin.merlin_transcript import MerlinTranscript
from py_ecc.secp256k1.secp256k1 import bytes_to_int

# https://merlin.cool/
class Transcript(MerlinTranscript):
    """
    NOTE:
    append:
    self.append_scalar(b"A_comm_1", a)
    
    squeeze:
    self.get_and_append_challenge(b"beta")
    """

    def append(self, label: bytes, item: bytes) -> None:
        self.append_message(label, item)

    def append_scalar(self, label: bytes, item: Scalar):
        self.append_message(label, item.n.to_bytes(32, "big"))

    def get_and_append_challenge(self, label: bytes) -> Scalar:
        while True:
            challenge_bytes = self.challenge_bytes(label, 255)
            f = Scalar(bytes_to_int(challenge_bytes))
            if f != Scalar.zero():  # Enforce challenge != 0
                self.append(label, challenge_bytes)
                return f
