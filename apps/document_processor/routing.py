from typing import Literal
import os

LAMBDA_MAX_MB = float(os.getenv("MAX_DOCUMENT_SIZE_LAMBDA_MB", "100"))


def decide_processor(size_mb: float) -> Literal["lambda", "ec2"]:
    """
    Return 'lambda' for small docs (<= threshold) and 'ec2' for large docs.
    Pure logic; no side effects; unit-testable.
    """
    return "ec2" if size_mb > LAMBDA_MAX_MB else "lambda"
