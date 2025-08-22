from typing import Dict, Optional
import os
import socket
import threading


class _Base:
    def increment(
        self, name: str, labels: Optional[Dict[str, str]] = None
    ) -> None:  # pragma: no cover
        pass


class Noop(_Base):
    pass


class StatsD(_Base):
    def __init__(self, addr: Optional[str]):
        host, _, port = (addr or "127.0.0.1:8125").partition(":")
        self.addr = (host or "127.0.0.1", int(port) if port else 8125)
        try:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        except Exception:
            self.sock = None

    def increment(self, name: str, labels: Optional[Dict[str, str]] = None) -> None:
        try:
            if not self.sock:
                return
            tag = ""
            if labels:
                tag = "|#" + ",".join(f"{k}:{v}" for k, v in sorted(labels.items()))
            self.sock.sendto(f"{name}:1|c{tag}".encode(), self.addr)
        except Exception:
            pass


_provider = None
_lock = threading.Lock()


def _select():
    backend = os.getenv("METRICS_BACKEND", "").lower()
    if backend == "statsd":
        return StatsD(os.getenv("METRICS_STATSD_ADDR"))
    return Noop()


def get_provider():
    global _provider
    with _lock:
        if _provider is None:
            _provider = _select()
        return _provider


def set_provider(p):  # test hook
    global _provider
    with _lock:
        _provider = p


def increment(name: str, labels: Optional[Dict[str, str]] = None) -> None:
    get_provider().increment(name, labels or {})
