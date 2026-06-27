import base64
import hashlib
import json
import shlex
import queue
import secrets
import socket
import os
import threading
import time
import traceback
from dataclasses import dataclass
from datetime import datetime, timedelta
from pathlib import Path
from typing import Callable, Dict, Optional

import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext, ttk

try:
    import winsound
except ImportError:
    winsound = None

from cryptography.fernet import Fernet, InvalidToken
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC


BUFFER_SIZE = 4096
PBKDF2_ITERATIONS = 500_000
MAX_MESSAGE_LENGTH = 1200
MAX_NAME_LENGTH = 24
GENERATED_PASSWORD_LENGTH = 24
MAX_CLIENTS = 20
MAX_FILE_SIZE = 4 * 1024 * 1024
KICK_BLOCK_SECONDS = 300
GAME_WIDTH = 900
GAME_HEIGHT = 500
GAME_PADDLE_WIDTH = 14
GAME_PADDLE_HEIGHT = 90
GAME_PADDLE_STEP = 26
GAME_BALL_SIZE = 14
GAME_PADDLE_MARGIN = 24
GAME_TICK_SECONDS = 1 / 30
IMAGE_FILE_TYPES = [
    ("PNG Images", "*.png"),
    ("GIF Images", "*.gif"),
    ("PPM Images", "*.ppm"),
    ("PGM Images", "*.pgm"),
]
def app_storage_dir() -> Path:
    local_appdata = os.environ.get("LOCALAPPDATA")
    if local_appdata:
        return Path(local_appdata) / "EncryptedChatRoom"
    return Path.home() / ".encrypted_chat_room"


APP_DIR = app_storage_dir()


def now_stamp() -> str:
    return datetime.now().strftime("%H:%M:%S")


def send_packet(sock: socket.socket, packet: dict) -> None:
    raw = (json.dumps(packet) + "\n").encode("utf-8")
    try:
        sock.sendall(raw)
        return True
    except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, OSError):
        return False


def format_addr(addr) -> str:
    host, port = addr[0], addr[1]
    return f"{host}:{port}"


def is_expected_disconnect_error(exc: Exception) -> bool:
    if isinstance(exc, (BrokenPipeError, ConnectionResetError, ConnectionAbortedError)):
        return True
    return getattr(exc, "winerror", None) in {10053, 10054}


def detect_lan_ip() -> str:
    try:
        probe = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            probe.connect(("8.8.8.8", 80))
            return probe.getsockname()[0]
        finally:
            probe.close()
    except Exception:
        return "unknown"


def generate_room_password(length: int = GENERATED_PASSWORD_LENGTH) -> str:
    alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789!@#$%^&*?"
    return "".join(secrets.choice(alphabet) for _ in range(length))


def safe_filename(text: str) -> str:
    cleaned = "".join(ch if ch.isalnum() or ch in {"-", "_"} else "_" for ch in text.strip())
    return cleaned.strip("_") or "room"


def moderation_state_path(server_name: str, port: int) -> Path:
    return APP_DIR / f"moderation_{safe_filename(server_name)}_{port}.json"


def safe_transfer_name(name: str) -> str:
    base_name = Path(name or "file").name.strip()
    cleaned = "".join(ch if ch.isalnum() or ch in {"-", "_", ".", " "} else "_" for ch in base_name)
    return cleaned.strip(" .") or "file"


def unique_destination(path: Path) -> Path:
    if not path.exists():
        return path
    stem = path.stem
    suffix = path.suffix
    counter = 1
    while True:
        candidate = path.with_name(f"{stem}_{counter}{suffix}")
        if not candidate.exists():
            return candidate
        counter += 1


def poster_fingerprint(name: str, ip_address: str) -> str:
    digest = hashlib.sha256(f"{name.strip().lower()}|{ip_address.strip()}".encode("utf-8")).hexdigest().upper()
    short = digest[:16]
    return "-".join(short[i : i + 4] for i in range(0, len(short), 4))


def derive_fernet(password: str, salt: bytes) -> Fernet:
    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=32,
        salt=salt,
        iterations=PBKDF2_ITERATIONS,
    )
    key = base64.urlsafe_b64encode(kdf.derive(password.encode("utf-8")))
    return Fernet(key)


def build_join_proof(name: str) -> dict:
    return {
        "proof": True,
        "name": name,
    }


@dataclass
class UiEvent:
    kind: str
    payload: dict


class ChatServer:
    def __init__(
        self,
        host: str,
        port: int,
        room_password: str,
        server_name: str,
        event_cb: Callable[[UiEvent], None],
        moderation_file: Path,
    ):
        self.host = host
        self.port = port
        self.server_name = server_name or "Host"
        self.event_cb = event_cb
        self.moderation_file = moderation_file
        self.salt = secrets.token_bytes(16)
        self.fernet = derive_fernet(room_password, self.salt)
        self.server_socket: Optional[socket.socket] = None
        self.running = False
        self.clients: Dict[socket.socket, dict] = {}
        self.blocked_names: Dict[str, str] = {}
        self.blocked_hosts: Dict[str, str] = {}
        self.kicked_names: Dict[str, float] = {}
        self.kicked_hosts: Dict[str, float] = {}
        self.moderator_ids: set[str] = set()
        self.game_active = False
        self.game_loop_thread: Optional[threading.Thread] = None
        self.game_session_counter = 0
        self.game_state = self._default_game_state()
        self.lock = threading.RLock()
        self._load_moderation_state()

    def _name_in_use_locked(self, name_key: str) -> bool:
        return any(info["name"].lower() == name_key for info in self.clients.values())

    def _find_client_locked(self, name: str) -> Optional[socket.socket]:
        target_name = name.strip().lower()
        for sock, info in self.clients.items():
            if info["name"].lower() == target_name:
                return sock
        return None

    def _prune_kicks_locked(self) -> None:
        now = time.time()
        self.kicked_names = {name: expires for name, expires in self.kicked_names.items() if expires > now}
        self.kicked_hosts = {host: expires for host, expires in self.kicked_hosts.items() if expires > now}

    def _kick_reason_locked(self, name_key: str, host_only: str) -> Optional[str]:
        self._prune_kicks_locked()
        expires = self.kicked_hosts.get(host_only) or self.kicked_names.get(name_key)
        if not expires:
            return None
        remaining = max(1, int(expires - time.time()))
        minutes, seconds = divmod(remaining, 60)
        if minutes:
            return f"kicked by the host for {minutes}m {seconds:02d}s"
        return f"kicked by the host for {seconds}s"

    def _resolve_target_locked(self, identifier: str) -> Optional[tuple[socket.socket, dict]]:
        lookup = identifier.strip().lower()
        if not lookup:
            return None
        exact_name_match = None
        poster_matches = []
        for sock, info in self.clients.items():
            if info["name"].lower() == lookup:
                exact_name_match = (sock, info)
                break
            poster_id = str(info.get("poster_id") or "").lower()
            if poster_id and poster_id.startswith(lookup):
                poster_matches.append((sock, info))
        if exact_name_match:
            return exact_name_match
        if len(poster_matches) == 1:
            return poster_matches[0]
        return None

    def _is_moderator_locked(self, poster_id: str) -> bool:
        return bool(poster_id) and poster_id in self.moderator_ids

    def _default_game_state(self) -> dict:
        return {
            "active": False,
            "pending": False,
            "status": "Idle",
            "message": "Open the room game to challenge someone.",
            "session_id": 0,
            "challenger_name": "",
            "challenger_id": "",
            "target_name": "",
            "target_id": "",
            "left_name": "",
            "left_id": "",
            "right_name": "",
            "right_id": "",
            "left_y": (GAME_HEIGHT - GAME_PADDLE_HEIGHT) // 2,
            "right_y": (GAME_HEIGHT - GAME_PADDLE_HEIGHT) // 2,
            "ball_x": GAME_WIDTH / 2,
            "ball_y": GAME_HEIGHT / 2,
            "ball_vx": 240.0,
            "ball_vy": 180.0,
            "left_score": 0,
            "right_score": 0,
            "last_tick": time.time(),
        }

    def _start_game_loop_locked(self) -> None:
        if self.game_loop_thread and self.game_loop_thread.is_alive():
            return
        self.game_loop_thread = threading.Thread(target=self._game_loop, daemon=True)
        self.game_loop_thread.start()

    def _broadcast_game_state_locked(self) -> None:
        payload = dict(self.game_state)
        payload["timestamp"] = now_stamp()
        snapshot = {"kind": "game_state", "state": payload}
        self._broadcast_encrypted(snapshot)

    def _game_loop(self) -> None:
        while self.running:
            time.sleep(GAME_TICK_SECONDS)
            with self.lock:
                if not self.game_state.get("active") or not self.clients:
                    continue
                now = time.time()
                last_tick = float(self.game_state.get("last_tick") or now)
                dt = max(0.0, min(0.2, now - last_tick))
                self.game_state["last_tick"] = now
                self._advance_game_locked(dt)
                self._broadcast_game_state_locked()

    def _advance_game_locked(self, dt: float) -> None:
        state = self.game_state
        ball_x = float(state.get("ball_x", GAME_WIDTH / 2))
        ball_y = float(state.get("ball_y", GAME_HEIGHT / 2))
        ball_vx = float(state.get("ball_vx", 240.0))
        ball_vy = float(state.get("ball_vy", 180.0))
        left_score = int(state.get("left_score", 0))
        right_score = int(state.get("right_score", 0))
        left_y = float(state.get("left_y", (GAME_HEIGHT - GAME_PADDLE_HEIGHT) / 2))
        right_y = float(state.get("right_y", (GAME_HEIGHT - GAME_PADDLE_HEIGHT) / 2))

        ball_x += ball_vx * dt
        ball_y += ball_vy * dt

        if ball_y <= 0:
            ball_y = 0
            ball_vy = abs(ball_vy)
        elif ball_y >= GAME_HEIGHT - GAME_BALL_SIZE:
            ball_y = GAME_HEIGHT - GAME_BALL_SIZE
            ball_vy = -abs(ball_vy)

        left_paddle_x = GAME_PADDLE_MARGIN
        right_paddle_x = GAME_WIDTH - GAME_PADDLE_MARGIN - GAME_PADDLE_WIDTH

        if ball_vx < 0 and ball_x <= left_paddle_x + GAME_PADDLE_WIDTH:
            if left_y <= ball_y + GAME_BALL_SIZE and ball_y <= left_y + GAME_PADDLE_HEIGHT:
                ball_x = left_paddle_x + GAME_PADDLE_WIDTH
                ball_vx = abs(ball_vx)
                offset = ((ball_y + GAME_BALL_SIZE / 2) - (left_y + GAME_PADDLE_HEIGHT / 2)) / max(1.0, GAME_PADDLE_HEIGHT / 2)
                ball_vy = max(-360.0, min(360.0, ball_vy + offset * 140.0))
            elif ball_x < 0:
                right_score += 1
                state["message"] = f"Point for {state.get('right_name') or 'right player'}."
                ball_x = GAME_WIDTH / 2
                ball_y = GAME_HEIGHT / 2
                ball_vx = 240.0
                ball_vy = 180.0 if secrets.randbelow(2) else -180.0

        if ball_vx > 0 and ball_x + GAME_BALL_SIZE >= right_paddle_x:
            if right_y <= ball_y + GAME_BALL_SIZE and ball_y <= right_y + GAME_PADDLE_HEIGHT:
                ball_x = right_paddle_x - GAME_BALL_SIZE
                ball_vx = -abs(ball_vx)
                offset = ((ball_y + GAME_BALL_SIZE / 2) - (right_y + GAME_PADDLE_HEIGHT / 2)) / max(1.0, GAME_PADDLE_HEIGHT / 2)
                ball_vy = max(-360.0, min(360.0, ball_vy + offset * 140.0))
            elif ball_x > GAME_WIDTH:
                left_score += 1
                state["message"] = f"Point for {state.get('left_name') or 'left player'}."
                ball_x = GAME_WIDTH / 2
                ball_y = GAME_HEIGHT / 2
                ball_vx = -240.0
                ball_vy = 180.0 if secrets.randbelow(2) else -180.0

        state["left_y"] = max(0, min(GAME_HEIGHT - GAME_PADDLE_HEIGHT, left_y))
        state["right_y"] = max(0, min(GAME_HEIGHT - GAME_PADDLE_HEIGHT, right_y))
        state["ball_x"] = ball_x
        state["ball_y"] = ball_y
        state["ball_vx"] = ball_vx
        state["ball_vy"] = ball_vy
        state["left_score"] = left_score
        state["right_score"] = right_score
        state["active"] = True
        state["status"] = "active"

    def _game_participant_info_locked(self, identifier: str) -> Optional[tuple[socket.socket, dict]]:
        resolved = self._resolve_target_locked(identifier)
        if not resolved:
            return None
        sock, info = resolved
        return sock, info

    def _game_player_side_locked(self, poster_id: str) -> Optional[str]:
        poster_id = poster_id.strip()
        if not poster_id:
            return None
        if poster_id == str(self.game_state.get("left_id") or ""):
            return "left"
        if poster_id == str(self.game_state.get("right_id") or ""):
            return "right"
        return None

    def _reset_game_to_idle_locked(self, message: str = "Open the room game to challenge someone.") -> None:
        self.game_active = False
        self.game_state = self._default_game_state()
        self.game_state["message"] = message

    def challenge_pong(self, challenger_sock: socket.socket, target_identifier: str) -> bool:
        identifier = target_identifier.strip()
        if not identifier:
            return False
        with self.lock:
            challenger_info = self.clients.get(challenger_sock)
            if not challenger_info:
                return False
            if self.game_state.get("pending") or self.game_state.get("active"):
                return False
            resolved = self._resolve_target_locked(identifier)
            if not resolved:
                return False
            target_sock, target_info = resolved
            challenger_id = str(challenger_info.get("poster_id") or "")
            target_id = str(target_info.get("poster_id") or "")
            if challenger_id == target_id:
                return False
            self.game_session_counter += 1
            self.game_state = self._default_game_state()
            self.game_state.update(
                {
                    "session_id": self.game_session_counter,
                    "pending": True,
                    "status": "pending",
                    "challenger_name": challenger_info["name"],
                    "challenger_id": challenger_id,
                    "target_name": target_info["name"],
                    "target_id": target_id,
                    "message": f"{challenger_info['name']} challenged {target_info['name']} to Pong.",
                }
            )
            self._broadcast_game_state_locked()
        self._send_encrypted_to_socket(
            target_sock,
            {
                "kind": "system",
                "message": f"{challenger_info['name']} challenged you to Pong. Use /acceptpong {challenger_info['name']} or /deny {challenger_info['name']}.",
                "timestamp": now_stamp(),
            },
        )
        self._send_encrypted_to_socket(
            challenger_sock,
            {
                "kind": "system",
                "message": f"Challenge sent to {target_info['name']}.",
                "timestamp": now_stamp(),
            },
        )
        return True

    def respond_pong(self, responder_sock: socket.socket, challenger_identifier: str, accept: bool) -> bool:
        identifier = challenger_identifier.strip()
        if not identifier:
            return False
        with self.lock:
            responder_info = self.clients.get(responder_sock)
            if not responder_info:
                return False
            pending = bool(self.game_state.get("pending"))
            if not pending:
                return False
            target_id = str(self.game_state.get("target_id") or "")
            if target_id and target_id != str(responder_info.get("poster_id") or ""):
                return False
            resolved = self._resolve_target_locked(identifier)
            if not resolved:
                return False
            challenger_sock, challenger_info = resolved
            challenger_id = str(challenger_info.get("poster_id") or "")
            if challenger_id != str(self.game_state.get("challenger_id") or ""):
                return False
            if not accept:
                challenger_name = str(challenger_info.get("name") or "Unknown")
                responder_name = str(responder_info.get("name") or "Unknown")
                self._reset_game_to_idle_locked(f"{responder_name} denied the Pong challenge from {challenger_name}.")
                self._broadcast_game_state_locked()
                self._broadcast_encrypted(
                    {
                        "kind": "system",
                        "message": f"{responder_name} denied the Pong challenge from {challenger_name}.",
                        "timestamp": now_stamp(),
                    }
                )
                return True
            session_id = int(self.game_state.get("session_id") or self.game_session_counter)
            self.game_state = self._default_game_state()
            self.game_state.update(
                {
                    "session_id": session_id,
                    "active": True,
                    "pending": False,
                    "status": "active",
                    "left_name": challenger_info["name"],
                    "left_id": challenger_id,
                    "right_name": responder_info["name"],
                    "right_id": str(responder_info.get("poster_id") or ""),
                    "left_y": (GAME_HEIGHT - GAME_PADDLE_HEIGHT) // 2,
                    "right_y": (GAME_HEIGHT - GAME_PADDLE_HEIGHT) // 2,
                    "ball_x": GAME_WIDTH / 2,
                    "ball_y": GAME_HEIGHT / 2,
                    "ball_vx": 240.0 if secrets.randbelow(2) else -240.0,
                    "ball_vy": 180.0 if secrets.randbelow(2) else -180.0,
                    "message": f"Pong started: {challenger_info['name']} vs {responder_info['name']}.",
                }
            )
            self.game_active = True
            self._start_game_loop_locked()
            self._broadcast_game_state_locked()
        self._broadcast_encrypted(
            {
                "kind": "system",
                "message": f"Pong started: {challenger_info['name']} vs {responder_info['name']}.",
                "timestamp": now_stamp(),
            }
        )
        return True

    def handle_game_action(self, sock: socket.socket, sender_name: str, action: dict) -> None:
        verb = str(action.get("action") or "").strip().lower()
        with self.lock:
            sender_info = self.clients.get(sock)
            if not sender_info:
                return
            sender_id = str(sender_info.get("poster_id") or "")
            if verb == "sync":
                self._send_encrypted_to_socket(sock, {"kind": "game_state", "state": dict(self.game_state), "timestamp": now_stamp()})
                return
            if verb == "move":
                if not self.game_state.get("active"):
                    return
                try:
                    dy = int(action.get("dy", 0))
                except (TypeError, ValueError):
                    dy = 0
                dy = max(-1, min(1, dy))
                if dy == 0:
                    return
                side = self._game_player_side_locked(sender_id)
                if side == "left":
                    self.game_state["left_y"] = max(
                        0,
                        min(GAME_HEIGHT - GAME_PADDLE_HEIGHT, int(self.game_state.get("left_y", 0)) + dy * GAME_PADDLE_STEP),
                    )
                elif side == "right":
                    self.game_state["right_y"] = max(
                        0,
                        min(GAME_HEIGHT - GAME_PADDLE_HEIGHT, int(self.game_state.get("right_y", 0)) + dy * GAME_PADDLE_STEP),
                    )
                else:
                    return
                self.game_state["message"] = f"{sender_name} moved their paddle."
                self.game_state["last_tick"] = time.time()
                self._broadcast_game_state_locked()

    def start(self) -> None:
        if self.running:
            return
        try:
            self.server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.server_socket.bind((self.host, self.port))
            self.server_socket.listen()
        except OSError as exc:
            self.server_socket = None
            raise RuntimeError(f"Could not start server on {self.host}:{self.port}: {exc}") from exc
        self.running = True
        threading.Thread(target=self._accept_loop, daemon=True).start()
        self.event_cb(UiEvent("server_status", {"text": f"Hosting on {self.host}:{self.port}"}))

    def stop(self) -> None:
        self.running = False
        with self.lock:
            sockets = list(self.clients.keys())
        for client in sockets:
            self._drop_client(client, announce=False)
        if self.server_socket:
            try:
                self.server_socket.close()
            except OSError:
                pass
            self.server_socket = None
        self.event_cb(UiEvent("server_status", {"text": "Server stopped"}))

    def _accept_loop(self) -> None:
        while self.running and self.server_socket:
            try:
                client_sock, addr = self.server_socket.accept()
                client_sock.settimeout(1.0)
                if not send_packet(
                    client_sock,
                    {
                        "type": "hello",
                        "salt": base64.b64encode(self.salt).decode("ascii"),
                        "server_name": self.server_name,
                    },
                ):
                    try:
                        client_sock.close()
                    except OSError:
                        pass
                    continue
                threading.Thread(target=self._client_loop, args=(client_sock, addr), daemon=True).start()
            except OSError as exc:
                if self.running:
                    self.event_cb(UiEvent("server_error", {"text": f"Accept failed: {exc}"}))
                break
            except Exception as exc:
                self.event_cb(UiEvent("server_error", {"text": f"Accept failed: {exc}"}))

    def _client_loop(self, sock: socket.socket, addr) -> None:
        peer = format_addr(addr)
        buffer = ""
        joined = False
        try:
            while self.running:
                try:
                    chunk = sock.recv(BUFFER_SIZE)
                except socket.timeout:
                    continue
                if not chunk:
                    break
                buffer += chunk.decode("utf-8")
                while "\n" in buffer:
                    line, buffer = buffer.split("\n", 1)
                    if not line.strip():
                        continue
                    try:
                        packet = json.loads(line)
                    except json.JSONDecodeError:
                        send_packet(sock, {"type": "error", "message": "Malformed packet."})
                        continue
                    if packet.get("type") == "join" and not joined:
                        name = (packet.get("name") or "Guest").strip()[:MAX_NAME_LENGTH]
                        if not name:
                            send_packet(sock, {"type": "error", "message": "Display name is required."})
                            return
                        proof = packet.get("proof") or ""
                        try:
                            proof_body = json.loads(self.fernet.decrypt(proof.encode("utf-8")).decode("utf-8"))
                        except (InvalidToken, json.JSONDecodeError, TypeError, ValueError):
                            send_packet(sock, {"type": "error", "message": "Room password verification failed."})
                            return
                        if proof_body.get("name") != name:
                            send_packet(sock, {"type": "error", "message": "Room proof did not match the display name."})
                            return
                        with self.lock:
                            host_only = addr[0]
                            joined_fingerprint = poster_fingerprint(name, host_only)
                            name_key = name.lower()
                            block_reason = (
                                self.blocked_hosts.get(host_only)
                                or self.blocked_names.get(name_key)
                                or self._kick_reason_locked(name_key, host_only)
                            )
                            if block_reason:
                                send_packet(
                                    sock,
                                    {"type": "error", "message": f"You cannot join this room ({block_reason})."},
                                )
                                return
                            if self._name_in_use_locked(name_key):
                                send_packet(
                                    sock,
                                    {"type": "error", "message": "That display name is already in use."},
                                )
                                return
                            if len(self.clients) >= MAX_CLIENTS:
                                send_packet(sock, {"type": "error", "message": f"Room is full ({MAX_CLIENTS} users max)."})
                                return
                            self.clients[sock] = {
                                "name": name,
                                "addr": peer,
                                "ip": host_only,
                                "poster_id": joined_fingerprint,
                            }
                        send_packet(sock, {"type": "joined", "message": "Connected to room.", "anon_id": joined_fingerprint})
                        joined = True
                        self._broadcast_encrypted(
                            {
                                "kind": "system",
                                "message": f"{name} joined from {peer} with poster ID {joined_fingerprint}",
                                "timestamp": now_stamp(),
                            }
                        )
                        self._send_roster_to_socket(sock)
                        self._broadcast_roster()
                    elif packet.get("type") == "message" and joined:
                        token = packet.get("token") or ""
                        try:
                            body = json.loads(self.fernet.decrypt(token.encode("utf-8")).decode("utf-8"))
                        except (InvalidToken, json.JSONDecodeError, TypeError, ValueError):
                            send_packet(sock, {"type": "error", "message": "Invalid encrypted message."})
                            continue
                        sender = self.clients.get(sock, {}).get("name", "Unknown")
                        kind = str(body.get("kind") or "chat").strip().lower()
                        if kind == "roster":
                            self._broadcast_roster()
                            continue
                        if kind == "file":
                            raw_name = safe_transfer_name(str(body.get("file_name") or "file"))
                            raw_data = body.get("data") or ""
                            try:
                                file_bytes = base64.b64decode(raw_data.encode("ascii"), validate=True)
                            except (ValueError, UnicodeEncodeError):
                                send_packet(sock, {"type": "error", "message": "Invalid file payload."})
                                continue
                            if not file_bytes:
                                send_packet(sock, {"type": "error", "message": "Cannot send an empty file."})
                                continue
                            if len(file_bytes) > MAX_FILE_SIZE:
                                send_packet(
                                    sock,
                                    {"type": "error", "message": f"Files can be at most {MAX_FILE_SIZE // (1024 * 1024)} MB."},
                                )
                                continue
                            self._broadcast_encrypted(
                                {
                                    "kind": "file",
                                    "name": sender,
                                    "poster_id": self.clients.get(sock, {}).get("poster_id", ""),
                                    "file_name": raw_name,
                                    "size": len(file_bytes),
                                    "data": raw_data,
                                    "timestamp": now_stamp(),
                                }
                            )
                        elif kind == "image":
                            raw_name = safe_transfer_name(str(body.get("file_name") or "image.png"))
                            raw_data = body.get("data") or ""
                            try:
                                image_bytes = base64.b64decode(raw_data.encode("ascii"), validate=True)
                            except (ValueError, UnicodeEncodeError):
                                send_packet(sock, {"type": "error", "message": "Invalid image payload."})
                                continue
                            if not image_bytes:
                                send_packet(sock, {"type": "error", "message": "Cannot send an empty image."})
                                continue
                            if len(image_bytes) > MAX_FILE_SIZE:
                                send_packet(
                                    sock,
                                    {"type": "error", "message": f"Images can be at most {MAX_FILE_SIZE // (1024 * 1024)} MB."},
                                )
                                continue
                            self._broadcast_encrypted(
                                {
                                    "kind": "image",
                                    "name": sender,
                                    "poster_id": self.clients.get(sock, {}).get("poster_id", ""),
                                    "file_name": raw_name,
                                    "size": len(image_bytes),
                                    "data": raw_data,
                                    "timestamp": now_stamp(),
                                }
                            )
                        elif kind == "game":
                            self.handle_game_action(sock, sender, body)
                        else:
                            message = str(body.get("message", "")).strip()[:MAX_MESSAGE_LENGTH]
                            sender_info = self.clients.get(sock, {})
                            poster_id = str(sender_info.get("poster_id") or "")
                            if message.startswith("/") and self._handle_client_command(sock, sender_info, message):
                                continue
                            outgoing = {
                                "kind": "chat",
                                "name": sender,
                                "poster_id": poster_id,
                                "message": message,
                                "timestamp": now_stamp(),
                            }
                            if outgoing["message"]:
                                self._broadcast_encrypted(outgoing)
                    else:
                        send_packet(sock, {"type": "error", "message": "Unexpected packet."})
        except OSError as exc:
            with self.lock:
                still_tracked = sock in self.clients
            if self.running and still_tracked and not is_expected_disconnect_error(exc):
                self.event_cb(UiEvent("server_error", {"text": f"{peer} disconnected unexpectedly: {exc}"}))
        except Exception as exc:
            self.event_cb(UiEvent("server_error", {"text": f"{peer} disconnected unexpectedly: {exc}"}))
        finally:
            self._drop_client(sock, announce=joined)

    def _broadcast_encrypted(self, body: dict) -> None:
        packet = {"type": "message", "token": self.fernet.encrypt(json.dumps(body).encode("utf-8")).decode("utf-8")}
        with self.lock:
            sockets = list(self.clients.keys())
        for sock in sockets:
            if not send_packet(sock, packet):
                self._drop_client(sock, announce=True)

    def _send_encrypted_to_socket(self, sock: socket.socket, body: dict) -> bool:
        packet = {"type": "message", "token": self.fernet.encrypt(json.dumps(body).encode("utf-8")).decode("utf-8")}
        if not send_packet(sock, packet):
            self._drop_client(sock, announce=True)
            return False
        return True

    def _build_roster_payload_locked(self) -> dict:
        roster = [
            {
                "name": info["name"],
                "poster_id": str(info.get("poster_id") or ""),
                "moderator": self._is_moderator_locked(str(info.get("poster_id") or "")),
            }
            for info in self.clients.values()
        ]
        roster.sort(key=lambda item: (item["name"].lower(), item["poster_id"]))
        return {
            "kind": "roster",
            "entries": roster,
            "names": [entry["name"] for entry in roster],
            "timestamp": now_stamp(),
        }

    def _send_roster_to_socket(self, sock: socket.socket) -> bool:
        with self.lock:
            payload = self._build_roster_payload_locked()
        return self._send_encrypted_to_socket(sock, payload)

    def _broadcast_roster(self) -> None:
        with self.lock:
            payload = self._build_roster_payload_locked()
        self._broadcast_encrypted(payload)

    def kick_user(self, name: str, actor_label: str = "the host") -> bool:
        identifier = name.strip()
        if not identifier:
            return False
        target_sock = None
        target_info = None
        with self.lock:
            resolved = self._resolve_target_locked(identifier)
            if resolved:
                target_sock, target_info = resolved
                expires_at = time.time() + KICK_BLOCK_SECONDS
                self.kicked_names[target_info["name"].lower()] = expires_at
                target_host = str(target_info.get("ip") or target_info["addr"].split(":", 1)[0])
                self.kicked_hosts[target_host] = expires_at
        if not target_sock:
            return False
        try:
            send_packet(
                target_sock,
                {"type": "error", "message": f"You were kicked by {actor_label} for {KICK_BLOCK_SECONDS // 60} minutes."},
            )
        except OSError:
            pass
        self._drop_client(target_sock, announce=True)
        return True

    def ban_user(self, name: str, actor_label: str = "the host") -> bool:
        identifier = name.strip()
        if not identifier:
            return False
        target_sock = None
        target_host = None
        target_name = None
        with self.lock:
            resolved = self._resolve_target_locked(identifier)
            if not resolved:
                return False
            target_sock, info = resolved
            target_name = info["name"].lower()
            target_host = str(info.get("ip") or info["addr"].split(":", 1)[0])
            self.blocked_names[target_name] = "banned by the host"
            if target_host:
                self.blocked_hosts[target_host] = "banned by the host"
            self._save_moderation_state()
        try:
            send_packet(target_sock, {"type": "error", "message": f"You were banned by {actor_label}."})
        except OSError:
            pass
        self._drop_client(target_sock, announce=True)
        return True

    def promote_user(self, name: str) -> bool:
        identifier = name.strip()
        if not identifier:
            return False
        target_name = None
        with self.lock:
            resolved = self._resolve_target_locked(identifier)
            if not resolved:
                return False
            _, target_info = resolved
            poster_id = str(target_info.get("poster_id") or "").strip()
            if not poster_id or poster_id in self.moderator_ids:
                return False
            self.moderator_ids.add(poster_id)
            target_name = target_info["name"]
        self._broadcast_encrypted(
            {
                "kind": "system",
                "message": f"{target_name} is now a moderator",
                "timestamp": now_stamp(),
            }
        )
        self._broadcast_roster()
        return True

    def demote_user(self, name: str) -> bool:
        identifier = name.strip()
        if not identifier:
            return False
        target_name = None
        removed = False
        with self.lock:
            resolved = self._resolve_target_locked(identifier)
            if not resolved:
                return False
            _, target_info = resolved
            poster_id = str(target_info.get("poster_id") or "").strip()
            if not poster_id:
                return False
            removed = poster_id in self.moderator_ids
            self.moderator_ids.discard(poster_id)
            target_name = target_info["name"]
        if removed:
            self._broadcast_encrypted(
                {
                    "kind": "system",
                    "message": f"{target_name} is no longer a moderator",
                    "timestamp": now_stamp(),
                }
            )
            self._broadcast_roster()
        return removed

    def _handle_client_command(self, sock: socket.socket, sender_info: dict, text: str) -> bool:
        try:
            parts = shlex.split(text)
        except ValueError:
            parts = text.split()
        if not parts:
            return False
        command = parts[0].lower()
        target_name = " ".join(parts[1:]).strip()
        sender_name = str(sender_info.get("name") or "Unknown")
        poster_id = str(sender_info.get("poster_id") or "").strip()
        is_moderator = self._is_moderator_locked(poster_id)
        if command == "/pong":
            if not target_name:
                send_packet(sock, {"type": "error", "message": "/pong requires a participant name or anonymous ID."})
                return True
            if not self.challenge_pong(sock, target_name):
                send_packet(sock, {"type": "error", "message": "Could not start a Pong challenge with that participant."})
            return True
        if command in {"/acceptpong", "/denypong", "/deny"}:
            if not target_name:
                send_packet(sock, {"type": "error", "message": f"{command} requires the challenger name or anonymous ID."})
                return True
            accepted = command == "/acceptpong"
            if not self.respond_pong(sock, target_name, accepted):
                send_packet(sock, {"type": "error", "message": "There is no matching Pong challenge to respond to."})
            return True
        if command == "/kick":
            if not is_moderator:
                send_packet(sock, {"type": "error", "message": "Only the host or a moderator can kick participants."})
                return True
            if not target_name:
                send_packet(sock, {"type": "error", "message": "/kick requires a participant name or anonymous ID."})
                return True
            if target_name.lower() == sender_name.lower():
                send_packet(sock, {"type": "error", "message": "You cannot kick yourself."})
                return True
            if not self.kick_user(target_name, actor_label=f"moderator {sender_name}"):
                send_packet(sock, {"type": "error", "message": "That participant or anonymous ID is no longer connected."})
            return True
        if command == "/ban":
            send_packet(sock, {"type": "error", "message": "Only the room host can ban participants."})
            return True
        if command == "/unban":
            send_packet(sock, {"type": "error", "message": "Only the room host can unban participants."})
            return True
        if command in {"/mod", "/unmod"}:
            send_packet(sock, {"type": "error", "message": "Only the room host can manage moderators."})
            return True
        return False

    def unban_user(self, label: str) -> bool:
        raw = label.strip()
        if not raw:
            return False
        with self.lock:
            self._prune_kicks_locked()
            name_key = raw.lower()
            resolved = self._resolve_target_locked(raw)
            if raw.startswith("Name: "):
                name_key = raw[6:].split(" (", 1)[0].strip().lower()
                removed = self.blocked_names.pop(name_key, None) is not None
                removed = self.kicked_names.pop(name_key, None) is not None or removed
            elif raw.startswith("IP: "):
                host_key = raw[4:].split(" (", 1)[0].strip()
                removed = self.blocked_hosts.pop(host_key, None) is not None
                removed = self.kicked_hosts.pop(host_key, None) is not None or removed
            elif resolved:
                _, info = resolved
                resolved_name = str(info.get("name") or "").strip().lower()
                resolved_host = str(info.get("ip") or info.get("addr", "").split(":", 1)[0]).strip()
                removed = self.blocked_names.pop(resolved_name, None) is not None
                removed = self.kicked_names.pop(resolved_name, None) is not None or removed
                if resolved_host:
                    removed = self.blocked_hosts.pop(resolved_host, None) is not None or removed
                    removed = self.kicked_hosts.pop(resolved_host, None) is not None or removed
            else:
                removed = self.blocked_names.pop(name_key, None) is not None
                removed = self.kicked_names.pop(name_key, None) is not None or removed
            if removed:
                self._save_moderation_state()
            return removed

    def get_blocked_labels(self) -> list[str]:
        with self.lock:
            self._prune_kicks_locked()
            labels = [f"Name: {name} ({reason})" for name, reason in sorted(self.blocked_names.items())]
            labels.extend(f"IP: {host} ({reason})" for host, reason in sorted(self.blocked_hosts.items()))
            labels.extend(
                f"Name: {name} (kick expires in {max(1, int(expires - time.time()))}s)"
                for name, expires in sorted(self.kicked_names.items())
            )
            labels.extend(
                f"IP: {host} (kick expires in {max(1, int(expires - time.time()))}s)"
                for host, expires in sorted(self.kicked_hosts.items())
            )
        return labels

    def _load_moderation_state(self) -> None:
        if not self.moderation_file.exists():
            self._save_moderation_state()
            return
        try:
            data = json.loads(self.moderation_file.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            self._save_moderation_state()
            return
        self.blocked_names = {
            str(name).lower(): str(reason)
            for name, reason in data.get("blocked_names", {}).items()
            if str(name).strip()
        }
        self.blocked_hosts = {
            str(host): str(reason)
            for host, reason in data.get("blocked_hosts", {}).items()
            if str(host).strip()
        }

    def _save_moderation_state(self) -> None:
        payload = {
            "blocked_names": self.blocked_names,
            "blocked_hosts": self.blocked_hosts,
        }
        self.moderation_file.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    def _drop_client(self, sock: socket.socket, announce: bool) -> None:
        client_name = None
        client_id = None
        reset_game = False
        reset_message = ""
        with self.lock:
            info = self.clients.pop(sock, None)
            if info:
                client_name = info["name"]
                client_id = str(info.get("poster_id") or "").strip()
                if client_id:
                    self.moderator_ids.discard(client_id)
                    if client_id in {
                        str(self.game_state.get("challenger_id") or ""),
                        str(self.game_state.get("target_id") or ""),
                        str(self.game_state.get("left_id") or ""),
                        str(self.game_state.get("right_id") or ""),
                    }:
                        reset_game = True
                        reset_message = f"{client_name} left the room game."
            if reset_game:
                self._reset_game_to_idle_locked(reset_message or "Open the room game to challenge someone.")
                self._broadcast_game_state_locked()
        try:
            sock.close()
        except OSError:
            pass
        if client_name and announce:
            self._broadcast_encrypted(
                {
                    "kind": "system",
                    "message": f"{client_name} left the room",
                    "timestamp": now_stamp(),
                }
            )
            self._broadcast_roster()


class ChatClient:
    def __init__(self, host: str, port: int, display_name: str, room_password: str, event_cb: Callable[[UiEvent], None]):
        self.host = host
        self.port = port
        self.display_name = display_name or "Guest"
        self.room_password = room_password
        self.event_cb = event_cb
        self.sock: Optional[socket.socket] = None
        self.running = False
        self.fernet: Optional[Fernet] = None
        self.anon_id: Optional[str] = None
        self.reader_thread: Optional[threading.Thread] = None
        self._buffer = ""
        self.capabilities = {"files": True, "images": True, "pong": True}

    def connect(self) -> None:
        try:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.settimeout(5.0)
            self.sock.connect((self.host, self.port))
            hello = self._read_packet_blocking()
            if hello.get("type") != "hello":
                raise RuntimeError("Server did not send a valid handshake.")
            salt = base64.b64decode(hello["salt"].encode("ascii"))
            self.fernet = derive_fernet(self.room_password, salt)
            proof = self.fernet.encrypt(json.dumps(build_join_proof(self.display_name)).encode("utf-8")).decode("utf-8")
            if not send_packet(
                self.sock,
                {
                    "type": "join",
                    "name": self.display_name,
                    "proof": proof,
                },
            ):
                raise RuntimeError("Could not send the join packet.")
            joined = self._read_packet_blocking()
            if joined.get("type") == "error":
                raise RuntimeError(joined.get("message", "Join failed."))
            if joined.get("type") != "joined":
                raise RuntimeError("Unexpected response from server.")
            self.sock.settimeout(1.0)
            self.running = True
            self.reader_thread = threading.Thread(target=self._read_loop, daemon=True)
            self.reader_thread.start()
            self.anon_id = joined.get("anon_id") or poster_fingerprint(self.display_name, self.host)
            self.request_roster()
            self.event_cb(UiEvent("client_status", {"text": f"Connected to {self.host}:{self.port} as {self.anon_id}"}))
        except Exception as exc:
            self.disconnect()
            raise RuntimeError(self._friendly_connect_error(exc)) from exc

    def disconnect(self) -> None:
        self.running = False
        if self.sock:
            try:
                self.sock.close()
            except OSError:
                pass
            self.sock = None
        self._clear_runtime_state()
        self.event_cb(UiEvent("client_status", {"text": "Disconnected"}))

    def _clear_runtime_state(self) -> None:
        self._buffer = "\0" * len(self._buffer)
        self._buffer = ""
        self.fernet = None
        self.anon_id = None
        self.reader_thread = None
        self.room_password = ""

    def send_chat(self, message: str) -> None:
        if not self.sock or not self.fernet:
            raise RuntimeError("Not connected.")
        trimmed = message.strip()
        if not trimmed:
            return
        if len(trimmed) > MAX_MESSAGE_LENGTH:
            raise RuntimeError(f"Messages can be at most {MAX_MESSAGE_LENGTH} characters.")
        body = {"message": trimmed}
        token = self.fernet.encrypt(json.dumps(body).encode("utf-8")).decode("utf-8")
        if not send_packet(self.sock, {"type": "message", "token": token}):
            raise RuntimeError("Could not send chat message.")

    def send_file(self, path: Path) -> None:
        if not self.sock or not self.fernet:
            raise RuntimeError("Not connected.")
        if not path.exists() or not path.is_file():
            raise RuntimeError("Choose a valid file.")
        file_size = path.stat().st_size
        if file_size <= 0:
            raise RuntimeError("Cannot send an empty file.")
        if file_size > MAX_FILE_SIZE:
            raise RuntimeError(f"Files can be at most {MAX_FILE_SIZE // (1024 * 1024)} MB.")
        payload = {
            "kind": "file",
            "file_name": safe_transfer_name(path.name),
            "data": base64.b64encode(path.read_bytes()).decode("ascii"),
        }
        token = self.fernet.encrypt(json.dumps(payload).encode("utf-8")).decode("utf-8")
        if not send_packet(self.sock, {"type": "message", "token": token}):
            raise RuntimeError("Could not send file.")

    def send_image(self, path: Path) -> None:
        if not self.sock or not self.fernet:
            raise RuntimeError("Not connected.")
        if not path.exists() or not path.is_file():
            raise RuntimeError("Choose a valid image file.")
        image_size = path.stat().st_size
        if image_size <= 0:
            raise RuntimeError("Cannot send an empty image.")
        if image_size > MAX_FILE_SIZE:
            raise RuntimeError(f"Images can be at most {MAX_FILE_SIZE // (1024 * 1024)} MB.")
        payload = {
            "kind": "image",
            "file_name": safe_transfer_name(path.name),
            "data": base64.b64encode(path.read_bytes()).decode("ascii"),
        }
        token = self.fernet.encrypt(json.dumps(payload).encode("utf-8")).decode("utf-8")
        if not send_packet(self.sock, {"type": "message", "token": token}):
            raise RuntimeError("Could not send image.")

    def send_game_action(self, action: str, dy: int = 0) -> None:
        if not self.sock or not self.fernet:
            raise RuntimeError("Not connected.")
        payload = {"kind": "game", "action": action}
        if action == "move":
            payload["dy"] = dy
        token = self.fernet.encrypt(json.dumps(payload).encode("utf-8")).decode("utf-8")
        if not send_packet(self.sock, {"type": "message", "token": token}):
            raise RuntimeError("Could not send game action.")

    def request_roster(self) -> None:
        if not self.sock or not self.fernet:
            raise RuntimeError("Not connected.")
        payload = {"kind": "roster", "timestamp": now_stamp()}
        token = self.fernet.encrypt(json.dumps(payload).encode("utf-8")).decode("utf-8")
        if not send_packet(self.sock, {"type": "message", "token": token}):
            raise RuntimeError("Could not request roster.")

    def _read_packet_blocking(self) -> dict:
        try:
            while "\n" not in self._buffer:
                chunk = self.sock.recv(BUFFER_SIZE)
                if not chunk:
                    raise RuntimeError("Connection closed.")
                self._buffer += chunk.decode("utf-8")
            line, self._buffer = self._buffer.split("\n", 1)
            return json.loads(line)
        except json.JSONDecodeError as exc:
            raise RuntimeError("Server sent malformed JSON.") from exc
        except OSError as exc:
            raise RuntimeError(f"Could not read from server: {exc}") from exc

    def _read_loop(self) -> None:
        try:
            while self.running and self.sock:
                try:
                    chunk = self.sock.recv(BUFFER_SIZE)
                except socket.timeout:
                    continue
                except OSError:
                    break
                if not chunk:
                    break
                self._buffer += chunk.decode("utf-8")
                while "\n" in self._buffer:
                    line, self._buffer = self._buffer.split("\n", 1)
                    if not line.strip():
                        continue
                    try:
                        packet = json.loads(line)
                    except json.JSONDecodeError:
                        self.event_cb(UiEvent("client_error", {"text": "Received malformed data from the server."}))
                        continue
                    if packet.get("type") == "message":
                        self._handle_message(packet)
                    elif packet.get("type") == "error":
                        self.event_cb(UiEvent("client_error", {"text": packet.get("message", "Unknown server error.")}))
        except OSError as exc:
            if self.running:
                self.event_cb(UiEvent("client_error", {"text": f"Connection lost: {exc}"}))
        except Exception as exc:
            self.event_cb(UiEvent("client_error", {"text": f"Connection lost: {exc}"}))
        finally:
            self.running = False
            self.event_cb(UiEvent("client_closed", {}))

    def _handle_message(self, packet: dict) -> None:
        if not self.fernet:
            return
        token = packet.get("token") or ""
        try:
            body = json.loads(self.fernet.decrypt(token.encode("utf-8")).decode("utf-8"))
        except (InvalidToken, json.JSONDecodeError, TypeError):
            self.event_cb(UiEvent("client_error", {"text": "Received a message that could not be decrypted."}))
            return
        self.event_cb(UiEvent("message", body))

    def _friendly_connect_error(self, exc: Exception) -> str:
        if isinstance(exc, socket.timeout):
            return "Connection timed out."
        if isinstance(exc, ConnectionRefusedError):
            return "Could not reach the server."
        if isinstance(exc, OSError):
            return f"Network error: {exc}"
        return str(exc) or exc.__class__.__name__


class ChatApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Encrypted Chat Room (ERTC)")
        self.root.geometry("1280x860")
        self.root.minsize(1180, 780)
        self.events: "queue.Queue[UiEvent]" = queue.Queue()
        self.server: Optional[ChatServer] = None
        self.client: Optional[ChatClient] = None
        self.connected = False
        self.is_hosting = False

        self.host_var = tk.StringVar(value="0.0.0.0")
        self.port_var = tk.StringVar(value="4444")
        self.name_var = tk.StringVar(value="DesktopDeck")
        self.room_pass_var = tk.StringVar(value="pass")
        self.status_var = tk.StringVar(value="Ready")
        self.server_name_var = tk.StringVar(value="Local Room")
        self.banner_var = tk.StringVar()
        self.access_start_var = tk.StringVar()
        self.access_end_var = tk.StringVar()
        self.download_dir_var = tk.StringVar(value="No save folder selected")
        self.lan_ip_var = tk.StringVar(value=f"PC LAN IP: {detect_lan_ip()}")
        self.expose_network_var = tk.BooleanVar(value=True)
        self.sound_enabled_var = tk.BooleanVar(value=True)
        self.moderation_path: Optional[Path] = None
        self.download_dir: Optional[Path] = None
        self.roster_entries: list[dict] = []
        self.chat_background_path: Optional[Path] = None
        self.chat_background_image: Optional[tk.PhotoImage] = None
        self.chat_background_item: Optional[int] = None
        self.chat_background_label_item: Optional[int] = None
        self.chat_media_refs: list[tk.PhotoImage] = []
        self.chat_cursor_y = 12
        self.game_window: Optional[tk.Toplevel] = None
        self.game_canvas: Optional[tk.Canvas] = None
        self.game_status_var = tk.StringVar(
            value='Use /pong "username" to challenge someone, then /acceptpong or /deny to answer.'
        )
        self.game_state: dict = {}
        self.game_window_token: Optional[str] = None
        self.chat_images = []
        self.host_schedule: Optional[dict] = None

        self._build_ui()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.after(100, self._drain_events)
        self.root.after(1000, self._check_host_schedule)

    def _build_ui(self) -> None:
        self.root.columnconfigure(0, weight=3)
        self.root.columnconfigure(1, weight=1)
        self.root.rowconfigure(1, weight=1)

        top = ttk.LabelFrame(self.root, text="Connection")
        top.grid(row=0, column=0, columnspan=2, sticky="nsew", padx=10, pady=10)
        for col in range(8):
            top.columnconfigure(col, weight=1)

        ttk.Label(top, text="Host").grid(row=0, column=0, padx=4, pady=4, sticky="w")
        ttk.Entry(top, textvariable=self.host_var).grid(row=0, column=1, padx=4, pady=4, sticky="ew")
        ttk.Label(top, text="Port").grid(row=0, column=2, padx=4, pady=4, sticky="w")
        ttk.Entry(top, textvariable=self.port_var, width=8).grid(row=0, column=3, padx=4, pady=4, sticky="ew")
        ttk.Label(top, text="Display Name").grid(row=0, column=4, padx=4, pady=4, sticky="w")
        ttk.Entry(top, textvariable=self.name_var).grid(row=0, column=5, padx=4, pady=4, sticky="ew")
        ttk.Label(top, text="Room Password").grid(row=0, column=6, padx=4, pady=4, sticky="w")
        password_row = ttk.Frame(top)
        password_row.grid(row=0, column=7, padx=4, pady=4, sticky="ew")
        password_row.columnconfigure(0, weight=1)
        ttk.Entry(password_row, textvariable=self.room_pass_var, show="*").grid(row=0, column=0, sticky="ew")
        ttk.Button(password_row, text="Generate", command=self.fill_generated_password).grid(row=0, column=1, padx=(6, 0))

        ttk.Label(top, text="Server Name").grid(row=1, column=0, padx=4, pady=4, sticky="w")
        ttk.Entry(top, textvariable=self.server_name_var).grid(row=1, column=1, columnspan=3, padx=4, pady=4, sticky="ew")
        ttk.Label(top, text="Banner").grid(row=1, column=4, padx=4, pady=4, sticky="w")
        ttk.Entry(top, textvariable=self.banner_var).grid(row=1, column=5, columnspan=3, padx=4, pady=4, sticky="ew")
        ttk.Label(top, text="Open Time").grid(row=2, column=0, padx=4, pady=4, sticky="w")
        ttk.Entry(top, textvariable=self.access_start_var).grid(row=2, column=1, padx=4, pady=4, sticky="ew")
        ttk.Label(top, text="Close Time").grid(row=2, column=2, padx=4, pady=4, sticky="w")
        ttk.Entry(top, textvariable=self.access_end_var).grid(row=2, column=3, padx=4, pady=4, sticky="ew")
        ttk.Checkbutton(top, text="Allow network access", variable=self.expose_network_var).grid(
            row=2, column=4, columnspan=2, padx=4, pady=4, sticky="w"
        )
        ttk.Label(top, text="Use 24-hour HH:MM or leave both blank").grid(
            row=3, column=0, columnspan=8, padx=4, pady=4, sticky="w"
        )

        self.host_button = ttk.Button(top, text="Host Room", command=self.host_room)
        self.host_button.grid(row=4, column=4, padx=4, pady=4, sticky="ew")
        self.join_button = ttk.Button(top, text="Join Room", command=self.join_room)
        self.join_button.grid(row=4, column=5, padx=4, pady=4, sticky="ew")
        self.disconnect_button = ttk.Button(top, text="Disconnect", command=self.disconnect)
        self.disconnect_button.grid(row=4, column=6, padx=4, pady=4, sticky="ew")
        ttk.Label(top, textvariable=self.status_var).grid(row=4, column=7, padx=4, pady=4, sticky="e")

        chat_frame = ttk.LabelFrame(self.root, text="Chat")
        chat_frame.grid(row=1, column=0, sticky="nsew", padx=(10, 5), pady=(0, 10))
        chat_frame.rowconfigure(0, weight=1)
        chat_frame.columnconfigure(0, weight=1)
        chat_frame.columnconfigure(1, weight=0)

        self.chat_box = tk.Canvas(chat_frame, highlightthickness=0, bg="#161616")
        self.chat_box.grid(row=0, column=0, sticky="nsew", padx=(6, 0), pady=6)
        chat_scroll = ttk.Scrollbar(chat_frame, orient="vertical", command=self.chat_box.yview)
        chat_scroll.grid(row=0, column=1, sticky="ns", padx=(0, 6), pady=6)
        self.chat_box.configure(yscrollcommand=chat_scroll.set)
        self.chat_box.bind("<Configure>", lambda _event: self._sync_chat_canvas())

        input_frame = ttk.Frame(chat_frame)
        input_frame.grid(row=1, column=0, sticky="ew", padx=6, pady=(0, 6))
        input_frame.columnconfigure(0, weight=1)

        self.message_entry = ttk.Entry(input_frame)
        self.message_entry.grid(row=0, column=0, sticky="ew", padx=(0, 6))
        self.message_entry.bind("<Return>", lambda _event: self.send_message())
        ttk.Button(input_frame, text="Send", command=self.send_message).grid(row=0, column=1, sticky="ew")
        self.send_file_button = ttk.Button(input_frame, text="Send File", command=self.send_file)
        self.send_file_button.grid(row=0, column=2, sticky="ew", padx=(6, 0))
        self.send_image_button = ttk.Button(input_frame, text="Send Image", command=self.send_image)
        self.send_image_button.grid(row=0, column=3, sticky="ew", padx=(6, 0))
        self.save_folder_button = ttk.Button(input_frame, text="Set Save Folder", command=self.choose_download_dir)
        self.save_folder_button.grid(row=0, column=4, sticky="ew", padx=(6, 0))
        ttk.Button(input_frame, text="Set Chat BG", command=self.choose_chat_background).grid(
            row=0, column=5, sticky="ew", padx=(6, 0)
        )
        ttk.Button(input_frame, text="Clear BG", command=self.clear_chat_background).grid(
            row=0, column=6, sticky="ew", padx=(6, 0)
        )
        ttk.Checkbutton(input_frame, text="Sound", variable=self.sound_enabled_var).grid(
            row=0, column=7, sticky="w", padx=(8, 0)
        )
        self.pong_button = ttk.Button(input_frame, text="Pong Game", command=self.toggle_room_game_window)
        self.pong_button.grid(
            row=0, column=8, sticky="ew", padx=(6, 0)
        )

        side = ttk.LabelFrame(self.root, text="Participants")
        side.grid(row=1, column=1, sticky="nsew", padx=(5, 10), pady=(0, 10))
        side.rowconfigure(0, weight=0)
        side.rowconfigure(1, weight=1)
        side.columnconfigure(0, weight=1)

        roster_header = ttk.Label(side, text="Live Roster")
        roster_header.grid(row=0, column=0, sticky="w", padx=6, pady=(6, 0))
        roster_frame = ttk.Frame(side)
        roster_frame.grid(row=1, column=0, sticky="nsew", padx=6, pady=(4, 6))
        roster_frame.rowconfigure(0, weight=1)
        roster_frame.columnconfigure(0, weight=1)
        self.user_list = tk.Listbox(roster_frame, height=12)
        self.user_list.grid(row=0, column=0, sticky="nsew")
        roster_scroll = ttk.Scrollbar(roster_frame, orient="vertical", command=self.user_list.yview)
        roster_scroll.grid(row=0, column=1, sticky="ns")
        self.user_list.configure(yscrollcommand=roster_scroll.set)

        help_text = (
            "How it works:\n"
            "- Host Room starts a local server; Join Room connects to one.\n"
            f"- Up to {MAX_CLIENTS} users can join the room.\n"
            "- Leave Allow network access on for phones and other devices on your Wi-Fi; turn it off for local-only use.\n"
            "- To expose the room beyond your network, you still need router/firewall forwarding and a unique password.\n"
            "- If you expose the room, forward the port, share the password privately, and use a unique password per room.\n"
            "- `/kick`, `/ban`, `/unban`, `/mod`, and `/unmod` are host commands; `/pong`, `/acceptpong`, and `/deny` run the 1v1 Pong challenge.\n"
            "- Each user gets a fingerprinted roster entry so the side panel shows who is connected.\n"
            "- Open Pong Game, then use Up/W and Down/S to move your paddle.\n"
            "- Chat, files, and images are encrypted, but network metadata still exists.\n"
            "- Use Set Chat BG to personalize the chat pane, and Set Save Folder to choose where files land."
        )
        ttk.Label(side, text=help_text, justify="left", wraplength=300).grid(row=2, column=0, sticky="ew", padx=6, pady=(0, 6))
        ttk.Label(side, textvariable=self.lan_ip_var, justify="left", wraplength=300).grid(
            row=3, column=0, sticky="ew", padx=6, pady=(0, 2)
        )
        ttk.Label(side, textvariable=self.download_dir_var, justify="left", wraplength=300).grid(
            row=4, column=0, sticky="ew", padx=6, pady=(0, 6)
        )
        self._update_admin_controls()

    def emit(self, event: UiEvent) -> None:
        self.events.put(event)

    def _drain_events(self) -> None:
        while True:
            try:
                event = self.events.get_nowait()
            except queue.Empty:
                break
            self._handle_event(event)
        self.root.after(100, self._drain_events)

    def _handle_event(self, event: UiEvent) -> None:
        if event.kind == "message":
            kind = event.payload.get("kind")
            if kind == "chat":
                poster_id = event.payload.get("poster_id", "")
                poster_label = f" [{poster_id}]" if poster_id else ""
                self._append_chat(
                    f"[{event.payload.get('timestamp', now_stamp())}] "
                    f"{event.payload.get('name', 'Unknown')}{poster_label}: {event.payload.get('message', '')}"
                )
                self._play_notification_sound(event.payload.get("name", ""))
            elif kind == "file":
                self._handle_incoming_file(event.payload)
                self._play_notification_sound(event.payload.get("name", ""))
            elif kind == "image":
                self._handle_incoming_image(event.payload)
                self._play_notification_sound(event.payload.get("name", ""))
            elif kind == "system":
                self._append_chat(f"[{event.payload.get('timestamp', now_stamp())}] * {event.payload.get('message', '')}")
                self._play_notification_sound()
            elif kind == "roster":
                self._update_roster(event.payload.get("entries", event.payload.get("names", [])))
            elif kind == "game_state":
                self.game_state = dict(event.payload.get("state") or {})
                if self._game_state_warrants_window(self.game_state):
                    self.open_room_game_window()
                self._render_game_state()
        elif event.kind in {"server_status", "client_status"}:
            self.status_var.set(event.payload.get("text", "Ready"))
            self._append_chat(f"[{now_stamp()}] * {event.payload.get('text', '')}")
        elif event.kind in {"server_error", "client_error"}:
            text = event.payload.get("text", "An error occurred.")
            self.status_var.set(text)
            self._append_chat(f"[{now_stamp()}] * ERROR: {text}")
            messagebox.showerror("Chat Error", text)
        elif event.kind == "client_closed":
            if self.connected:
                self.connected = False
                self.status_var.set("Disconnected")

    def _append_chat(self, text: str) -> None:
        self._append_canvas_text(text)

    def _append_chat_image(self, text: str, image_data: str) -> None:
        try:
            image = tk.PhotoImage(data=image_data)
        except tk.TclError as exc:
            self._append_chat(f"[{now_stamp()}] * ERROR: Could not display image ({exc}).")
            return
        self.chat_images.append(image)
        self.chat_media_refs.append(image)
        self._append_canvas_text(text)
        self._append_canvas_image(image)

    def _play_notification_sound(self, sender_name: str = "") -> None:
        if not self.sound_enabled_var.get():
            return
        local_name = (self.name_var.get().strip() or "User")[:MAX_NAME_LENGTH].lower()
        if sender_name and sender_name.strip().lower() == local_name:
            return
        if winsound is None:
            return
        try:
            winsound.MessageBeep(winsound.MB_OK)
        except Exception:
            try:
                winsound.MessageBeep()
            except Exception:
                pass

    def _game_state_warrants_window(self, state: dict) -> bool:
        local_id = str(self.client.anon_id).strip() if self.client and self.client.anon_id else ""
        if not local_id:
            return False
        relevant_ids = {
            str(state.get("challenger_id") or "").strip(),
            str(state.get("target_id") or "").strip(),
            str(state.get("left_id") or "").strip(),
            str(state.get("right_id") or "").strip(),
        }
        if local_id not in relevant_ids:
            return False
        if not (state.get("pending") or state.get("active")):
            self.game_window_token = None
            return False
        token = "|".join(
            [
                str(state.get("session_id") or ""),
                str(state.get("status") or ""),
                str(state.get("challenger_id") or ""),
                str(state.get("target_id") or ""),
                str(state.get("left_id") or ""),
                str(state.get("right_id") or ""),
            ]
        )
        if token == self.game_window_token:
            return False
        self.game_window_token = token
        return True

    def _append_canvas_text(self, text: str) -> None:
        self.chat_box.update_idletasks()
        wrap_width = max(260, self.chat_box.winfo_width() - 28)
        x = 12
        y = self.chat_cursor_y
        shadow = self.chat_box.create_text(
            x + 1,
            y + 1,
            anchor="nw",
            text=text,
            width=wrap_width,
            fill="#000000",
        )
        item = self.chat_box.create_text(
            x,
            y,
            anchor="nw",
            text=text,
            width=wrap_width,
            fill="#f0f0f0",
        )
        self.chat_box.tag_raise(item)
        bbox = self.chat_box.bbox(item) or self.chat_box.bbox(shadow)
        if bbox:
            self.chat_cursor_y = bbox[3] + 8
        else:
            self.chat_cursor_y += 24
        self._sync_chat_canvas()

    def _append_canvas_image(self, image: tk.PhotoImage) -> None:
        self.chat_box.update_idletasks()
        x = 12
        y = self.chat_cursor_y
        item = self.chat_box.create_image(x, y, anchor="nw", image=image)
        bbox = self.chat_box.bbox(item)
        if bbox:
            self.chat_cursor_y = bbox[3] + 8
        else:
            self.chat_cursor_y += max(24, image.height() + 8)
        self._sync_chat_canvas()

    def _sync_chat_canvas(self) -> None:
        if self.chat_background_image and self.chat_background_item is None:
            self.chat_background_item = self.chat_box.create_image(
                0, 0, anchor="nw", image=self.chat_background_image, tags=("chat_background",)
            )
            self.chat_box.lower("chat_background")
        bbox = self.chat_box.bbox("all")
        if bbox:
            self.chat_box.configure(scrollregion=bbox)
        else:
            self.chat_box.configure(scrollregion=(0, 0, max(self.chat_box.winfo_width(), 1), max(self.chat_box.winfo_height(), 1)))
        self.chat_box.yview_moveto(1.0)

    def choose_chat_background(self) -> None:
        selected = filedialog.askopenfilename(
            title="Choose a chat background image",
            filetypes=IMAGE_FILE_TYPES,
        )
        if not selected:
            return
        try:
            image = tk.PhotoImage(file=selected)
        except tk.TclError as exc:
            messagebox.showerror("Background Failed", f"Could not load background image:\n{exc}")
            return
        self.chat_background_path = Path(selected)
        self.chat_background_image = image
        if self.chat_background_item is not None:
            self.chat_box.delete("chat_background")
            self.chat_background_item = None
        self.chat_background_item = self.chat_box.create_image(
            0, 0, anchor="nw", image=self.chat_background_image, tags=("chat_background",)
        )
        self.chat_box.lower("chat_background")
        self._sync_chat_canvas()
        self.status_var.set(f"Chat background set to {self.chat_background_path.name}")

    def clear_chat_background(self) -> None:
        self.chat_background_path = None
        self.chat_background_image = None
        self.chat_box.delete("chat_background")
        self.chat_background_item = None
        self._sync_chat_canvas()
        self.status_var.set("Chat background cleared")

    def toggle_room_game_window(self) -> None:
        if self.game_window and self.game_window.winfo_exists():
            self.close_room_game_window()
            return
        self.open_room_game_window()

    def open_room_game_window(self) -> None:
        if self.game_window and self.game_window.winfo_exists():
            self.game_window.lift()
            self.game_window.focus_force()
            return
        self.game_window = tk.Toplevel(self.root)
        self.game_window.title("ERTC Room Game")
        self.game_window.geometry("960x500")
        self.game_window.resizable(False, False)
        self.game_window.protocol("WM_DELETE_WINDOW", self.close_room_game_window)

        outer = ttk.Frame(self.game_window)
        outer.pack(fill="both", expand=True)

        title = ttk.Label(outer, text="Room Pong", font=("TkDefaultFont", 14, "bold"))
        title.pack(anchor="w", padx=10, pady=(10, 4))

        how_to_play = ttk.Label(
            outer,
            text='How to play: challenge with /pong "username"; the target uses /acceptpong or /deny; move with Up/W and Down/S.',
            wraplength=920,
            justify="left",
        )
        how_to_play.pack(anchor="w", padx=10, pady=(0, 8))

        self.game_canvas = tk.Canvas(outer, width=GAME_WIDTH, height=GAME_HEIGHT, bg="#10131c", highlightthickness=0)
        self.game_canvas.pack(padx=10, pady=(0, 8))

        control_row = ttk.Frame(outer)
        control_row.pack(fill="x", padx=10)
        ttk.Button(control_row, text="Move Up", command=lambda: self.send_room_game_move(-1)).pack(side="left")
        ttk.Button(control_row, text="Move Down", command=lambda: self.send_room_game_move(1)).pack(side="left", padx=(8, 0))
        ttk.Button(control_row, text="Close Game", command=self.close_room_game_window).pack(side="right")

        ttk.Label(outer, textvariable=self.game_status_var, justify="left").pack(anchor="w", padx=10, pady=(8, 10))

        self.game_window.bind("<Up>", lambda _event: self.send_room_game_move(-1))
        self.game_window.bind("<Down>", lambda _event: self.send_room_game_move(1))
        self.game_window.bind("<w>", lambda _event: self.send_room_game_move(-1))
        self.game_window.bind("<s>", lambda _event: self.send_room_game_move(1))
        self.game_window.bind("<Escape>", lambda _event: self.close_room_game_window())
        self.game_window.focus_force()

        self._request_room_game_sync()
        self._render_game_state()

    def close_room_game_window(self) -> None:
        if self.game_window and self.game_window.winfo_exists():
            self.game_window.destroy()
        self.game_window = None
        self.game_canvas = None

    def _request_room_game_sync(self) -> None:
        if not self.client or not self.connected:
            self.game_status_var.set("Join a room to play Room Pong.")
            return
        try:
            self.client.send_game_action("sync")
        except Exception as exc:
            self.game_status_var.set(f"Game connection failed: {exc}")

    def send_room_game_move(self, dy: int) -> None:
        if not self.client or not self.connected:
            self.game_status_var.set("Join a room before moving the paddle.")
            return
        role = self._local_game_role()
        if role not in {"left", "right"}:
            self.game_status_var.set("You are not one of the two players in this game.")
            return
        try:
            self.client.send_game_action("move", dy)
        except Exception as exc:
            self.game_status_var.set(f"Game move failed: {exc}")

    def _local_game_role(self) -> str:
        if not self.client or not self.client.anon_id:
            return ""
        local_id = str(self.client.anon_id).strip()
        state = self.game_state or {}
        if local_id and local_id == str(state.get("left_id") or ""):
            return "left"
        if local_id and local_id == str(state.get("right_id") or ""):
            return "right"
        return ""

    def _render_game_state(self) -> None:
        if not self.game_canvas or not (self.game_window and self.game_window.winfo_exists()):
            return
        canvas = self.game_canvas
        canvas.delete("all")
        width = GAME_WIDTH
        height = GAME_HEIGHT
        state = self.game_state or {}
        left_y = float(state.get("left_y", (height - GAME_PADDLE_HEIGHT) // 2))
        right_y = float(state.get("right_y", (height - GAME_PADDLE_HEIGHT) // 2))
        ball_x = float(state.get("ball_x", width / 2))
        ball_y = float(state.get("ball_y", height / 2))
        left_score = int(state.get("left_score", 0))
        right_score = int(state.get("right_score", 0))
        message = str(state.get("message") or "Room Pong")
        left_name = str(state.get("left_name") or "Left")
        right_name = str(state.get("right_name") or "Right")
        role = self._local_game_role()
        role_text = "You are spectating."
        if role == "left":
            role_text = "You control the left paddle."
        elif role == "right":
            role_text = "You control the right paddle."
        self.game_status_var.set(f"{message}   Score {left_name} {left_score} - {right_score} {right_name}   {role_text}")

        canvas.create_rectangle(8, 8, width - 8, height - 8, outline="#3d4661", width=2)
        for x in range(24, width - 24, 36):
            canvas.create_line(x, 20, x, height - 20, fill="#1f2537", dash=(3, 6))
        canvas.create_line(width / 2, 20, width / 2, height - 20, fill="#242a3d", dash=(6, 8))
        canvas.create_text(16, 14, anchor="nw", text=f"{left_name}: {left_score}", fill="#dce6ff", font=("TkDefaultFont", 10, "bold"))
        canvas.create_text(width - 16, 14, anchor="ne", text=f"{right_name}: {right_score}", fill="#dce6ff", font=("TkDefaultFont", 10, "bold"))

        left_paddle_x = GAME_PADDLE_MARGIN
        right_paddle_x = width - GAME_PADDLE_MARGIN - GAME_PADDLE_WIDTH
        canvas.create_text(left_paddle_x + 7, 38, text=left_name, fill="#9fb4ff", font=("TkDefaultFont", 9))
        canvas.create_text(width - GAME_PADDLE_MARGIN - 7, 38, text=right_name, fill="#9fb4ff", font=("TkDefaultFont", 9))
        canvas.create_rectangle(
            left_paddle_x,
            left_y,
            left_paddle_x + GAME_PADDLE_WIDTH,
            left_y + GAME_PADDLE_HEIGHT,
            fill="#7bc6ff",
            outline="#d8f0ff",
            width=1,
        )
        canvas.create_rectangle(
            right_paddle_x,
            right_y,
            right_paddle_x + GAME_PADDLE_WIDTH,
            right_y + GAME_PADDLE_HEIGHT,
            fill="#ff9f7b",
            outline="#ffe2d8",
            width=1,
        )
        canvas.create_oval(
            ball_x,
            ball_y,
            ball_x + GAME_BALL_SIZE,
            ball_y + GAME_BALL_SIZE,
            fill="#ffffff",
            outline="#d4d4d4",
        )
        canvas.create_text(
            width / 2,
            height - 10,
            text="Use W/S or Up/Down to move your paddle. Only the two accepted players can control this game.",
            fill="#b7bfd6",
            font=("TkDefaultFont", 9),
        )

    def _scrub_widget_text(self, widget) -> None:
        current = widget.get()
        if current:
            widget.delete(0, "end")
            widget.insert(0, "\0" * len(current))
            widget.delete(0, "end")

    def _scrub_chat_box(self) -> None:
        self.chat_box.delete("all")
        self.chat_cursor_y = 12
        self.chat_media_refs.clear()
        self.chat_images.clear()
        if self.chat_background_image is not None:
            self.chat_background_item = self.chat_box.create_image(
                0, 0, anchor="nw", image=self.chat_background_image, tags=("chat_background",)
            )
            self.chat_box.lower("chat_background")
        self._sync_chat_canvas()

    def _clear_pending_events(self) -> None:
        while True:
            try:
                self.events.get_nowait()
            except queue.Empty:
                break

    def _best_effort_memory_scrub(self) -> None:
        self._scrub_chat_box()
        self._scrub_widget_text(self.message_entry)
        self.chat_images.clear()
        self.close_room_game_window()
        self.game_state = {}
        self.game_window_token = None
        self._update_roster([])
        self._clear_pending_events()
        self.room_pass_var.set("\0" * len(self.room_pass_var.get()))
        self.room_pass_var.set("")
        self.banner_var.set("\0" * len(self.banner_var.get()))
        self.banner_var.set("")

    def _handle_incoming_file(self, payload: dict) -> None:
        sender = str(payload.get("name") or "Unknown")
        poster_id = str(payload.get("poster_id") or "").strip()
        poster_label = f" [{poster_id}]" if poster_id else ""
        file_name = safe_transfer_name(str(payload.get("file_name") or "file"))
        encoded = payload.get("data") or ""
        try:
            file_bytes = base64.b64decode(encoded.encode("ascii"), validate=True)
        except (ValueError, UnicodeEncodeError):
            self._append_chat(f"[{now_stamp()}] * ERROR: Received an invalid file from {sender}.")
            return
        if not file_bytes:
            self._append_chat(f"[{now_stamp()}] * ERROR: Received an empty file from {sender}.")
            return
        if len(file_bytes) > MAX_FILE_SIZE:
            self._append_chat(f"[{now_stamp()}] * ERROR: Rejected oversized file from {sender}.")
            return
        if self.client and sender.lower() == self.client.display_name.lower():
            self._append_chat(
                f"[{payload.get('timestamp', now_stamp())}] * You{poster_label} sent file: {file_name} ({len(file_bytes)} bytes)"
            )
            return
        destination_dir = self._ensure_download_dir()
        if not destination_dir:
            self._append_chat(
                f"[{payload.get('timestamp', now_stamp())}] * File from {sender} was not saved because no folder was chosen."
            )
            return
        destination_dir.mkdir(parents=True, exist_ok=True)
        destination = unique_destination(destination_dir / file_name)
        destination.write_bytes(file_bytes)
        self._append_chat(
            f"[{payload.get('timestamp', now_stamp())}] * {sender}{poster_label} sent file: {destination.name} ({len(file_bytes)} bytes)"
        )
        self.status_var.set(f"Saved file to {destination}")

    def _handle_incoming_image(self, payload: dict) -> None:
        sender = str(payload.get("name") or "Unknown")
        poster_id = str(payload.get("poster_id") or "").strip()
        poster_label = f" [{poster_id}]" if poster_id else ""
        file_name = safe_transfer_name(str(payload.get("file_name") or "image.png"))
        encoded = payload.get("data") or ""
        try:
            image_bytes = base64.b64decode(encoded.encode("ascii"), validate=True)
        except (ValueError, UnicodeEncodeError):
            self._append_chat(f"[{now_stamp()}] * ERROR: Received an invalid image from {sender}.")
            return
        if not image_bytes:
            self._append_chat(f"[{now_stamp()}] * ERROR: Received an empty image from {sender}.")
            return
        if len(image_bytes) > MAX_FILE_SIZE:
            self._append_chat(f"[{now_stamp()}] * ERROR: Rejected oversized image from {sender}.")
            return
        author = "You" if self.client and sender.lower() == self.client.display_name.lower() else sender
        self._append_chat_image(
            f"[{payload.get('timestamp', now_stamp())}] * {author}{poster_label} sent image: {file_name} ({len(image_bytes)} bytes)",
            encoded,
        )
        self.status_var.set(f"Displayed image from {sender}")

    def choose_download_dir(self) -> None:
        selected = filedialog.askdirectory(title="Choose where incoming files should be saved")
        if not selected:
            return
        self.download_dir = Path(selected)
        self.download_dir_var.set(f"Incoming files folder: {self.download_dir}")
        self.status_var.set(f"Incoming files will be saved to {self.download_dir}")

    def _ensure_download_dir(self) -> Optional[Path]:
        if self.download_dir:
            return self.download_dir
        selected = filedialog.askdirectory(title="Choose where incoming files should be saved")
        if not selected:
            self.status_var.set("Incoming file save cancelled")
            return None
        self.download_dir = Path(selected)
        self.download_dir_var.set(f"Incoming files folder: {self.download_dir}")
        return self.download_dir

    def _update_roster(self, names) -> None:
        self.roster_entries = []
        self.user_list.delete(0, "end")
        if not names:
            self.user_list.insert("end", "No users connected")
            return
        for entry in names:
            if isinstance(entry, dict):
                name = str(entry.get("name") or "Unknown")
                poster_id = str(entry.get("poster_id") or "")
            else:
                name = str(entry)
                poster_id = ""
            self.roster_entries.append({"name": name, "poster_id": poster_id})
            label = f"{name} [{poster_id}]" if poster_id else name
            self.user_list.insert("end", label)

    def _selected_roster_entry(self) -> Optional[dict]:
        selection = self.user_list.curselection()
        if not selection:
            return None
        index = selection[0]
        if index < 0 or index >= len(self.roster_entries):
            return None
        return self.roster_entries[index]

    def _update_admin_controls(self) -> None:
        connected = bool(self.client and self.connected)
        capabilities = getattr(self.client, "capabilities", {}) if self.client else {}
        supports_files = connected and bool(capabilities.get("files", True))
        supports_images = connected and bool(capabilities.get("images", True))
        supports_pong = connected and bool(capabilities.get("pong", True))
        self.send_file_button.configure(state="normal" if supports_files else "disabled")
        self.send_image_button.configure(state="normal" if supports_images else "disabled")
        self.save_folder_button.configure(state="normal" if supports_files else "disabled")
        self.pong_button.configure(state="normal" if supports_pong else "disabled")
        if not supports_pong and self.game_window and self.game_window.winfo_exists():
            self.close_room_game_window()

    def fill_generated_password(self) -> None:
        password = generate_room_password()
        self.room_pass_var.set(password)
        self.root.clipboard_clear()
        self.root.clipboard_append(password)
        self.status_var.set("Generated a strong room password and copied it to the clipboard")

    def _validate_inputs(self) -> Optional[tuple]:
        host = self.host_var.get().strip()
        password = self.room_pass_var.get().strip()
        name = (self.name_var.get().strip() or "User")[:MAX_NAME_LENGTH]
        try:
            port = int(self.port_var.get().strip())
        except ValueError:
            messagebox.showwarning("Missing Info", "Port must be a number.")
            return None
        if not host:
            messagebox.showwarning("Missing Info", "Host is required.")
            return None
        if not password:
            messagebox.showwarning("Missing Info", "Room password is required.")
            return None
        return host, port, name, password

    def _parse_schedule_time(self, value: str, label: str) -> Optional[datetime]:
        text = value.strip()
        if not text:
            return None
        try:
            parsed = datetime.strptime(text, "%H:%M")
        except ValueError as exc:
            raise RuntimeError(f"{label} must use 24-hour HH:MM format.") from exc
        now = datetime.now()
        return now.replace(hour=parsed.hour, minute=parsed.minute, second=0, microsecond=0)

    def _build_host_schedule(self, host: str, port: int, name: str, password: str) -> Optional[dict]:
        start_at = self._parse_schedule_time(self.access_start_var.get(), "Open time")
        end_at = self._parse_schedule_time(self.access_end_var.get(), "Close time")
        banner = self.banner_var.get().strip()[:MAX_MESSAGE_LENGTH]
        if bool(start_at) != bool(end_at):
            raise RuntimeError("Set both Open Time and Close Time, or leave both blank.")
        if not start_at or not end_at:
            return None
        now = datetime.now()
        if end_at <= start_at:
            end_at += timedelta(days=1)
        elif now >= end_at:
            start_at += timedelta(days=1)
            end_at += timedelta(days=1)
        server_name = self.server_name_var.get().strip() or "Local Room"
        return {
            "host": host,
            "port": port,
            "name": name,
            "password": password,
            "server_name": server_name,
            "banner": banner,
            "moderation_path": moderation_state_path(server_name, port),
            "start_at": start_at,
            "end_at": end_at,
        }

    def _start_host_session(self, config: dict) -> None:
        self.moderation_path = config["moderation_path"]
        self.server = ChatServer(
            config["host"],
            config["port"],
            config["password"],
            config["server_name"],
            self.emit,
            self.moderation_path,
        )
        try:
            self.server.start()
            local_join_host = "127.0.0.1" if config["host"] in {"0.0.0.0", "*"} else config["host"]
            self.client = ChatClient(local_join_host, config["port"], config["name"], config["password"], self.emit)
            self.client.connect()
            self.connected = True
            self.is_hosting = True
            self.status_var.set(f"Hosting on {config['host']}:{config['port']}")
            banner = str(config.get("banner") or "").strip()
            if banner and self.server:
                self.server._broadcast_encrypted(
                    {
                        "kind": "system",
                        "message": f"Banner: {banner}",
                        "timestamp": now_stamp(),
                    }
                )
            self._update_admin_controls()
        except Exception:
            self._safe_stop_server()
            if self.client:
                self.client.disconnect()
                self.client = None
            self.connected = False
            self.is_hosting = False
            raise

    def host_room(self) -> None:
        if self.connected or self.host_schedule:
            messagebox.showinfo("Already Connected", "Disconnect before starting a new room.")
            return
        values = self._validate_inputs()
        if not values:
            return
        host, port, name, password = values
        host = "0.0.0.0" if self.expose_network_var.get() else "127.0.0.1"
        try:
            schedule = self._build_host_schedule(host, port, name, password)
            if schedule:
                self.host_schedule = schedule
                if datetime.now() >= schedule["start_at"]:
                    self._start_host_session(schedule)
                else:
                    self.is_hosting = True
                    self.status_var.set(
                        "Scheduled room access "
                        f"{schedule['start_at'].strftime('%Y-%m-%d %H:%M')} to {schedule['end_at'].strftime('%Y-%m-%d %H:%M')}"
                    )
                    self._append_chat(
                        f"[{now_stamp()}] * Room scheduled to open at {schedule['start_at'].strftime('%Y-%m-%d %H:%M')} "
                        f"and close at {schedule['end_at'].strftime('%Y-%m-%d %H:%M')}"
                    )
                    self._update_admin_controls()
            else:
                self._start_host_session(
                    {
                        "host": host,
                        "port": port,
                        "name": name,
                        "password": password,
                        "server_name": self.server_name_var.get().strip() or "Local Room",
                        "banner": self.banner_var.get().strip()[:MAX_MESSAGE_LENGTH],
                        "moderation_path": moderation_state_path(self.server_name_var.get().strip() or "Local Room", port),
                    }
                )
        except Exception as exc:
            self._safe_stop_server()
            self.is_hosting = False
            self.host_schedule = None
            self.moderation_path = None
            self._update_admin_controls()
            messagebox.showerror("Host Failed", f"Could not host room:\n{exc}")
            self.status_var.set("Host failed")

    def join_room(self) -> None:
        if self.host_schedule and not self.connected:
            messagebox.showinfo(
                "Scheduled Host Pending",
                "Disconnect the scheduled room setup before joining a different room.",
            )
            return
        if self.connected:
            messagebox.showinfo("Already Connected", "Disconnect before joining a different room.")
            return
        values = self._validate_inputs()
        if not values:
            return
        host, port, name, password = values
        try:
            self.client = ChatClient(host, port, name, password, self.emit)
            self.client.connect()
            self.connected = True
            self.is_hosting = False
            self.status_var.set(f"Joined {host}:{port}")
            self._update_admin_controls()
        except Exception as exc:
            if self.client:
                self.client.disconnect()
                self.client = None
            self.is_hosting = False
            self._update_admin_controls()
            messagebox.showerror("Join Failed", f"Could not join room:\n{exc}")
            self.status_var.set("Join failed")

    def send_message(self) -> None:
        text = self.message_entry.get().strip()
        if not text:
            return
        if not self.client or not self.connected:
            messagebox.showinfo("Not Connected", "Host or join a room before sending messages.")
            return
        try:
            if text.startswith("/") and self.is_hosting and self.server:
                try:
                    parts = shlex.split(text)
                except ValueError:
                    parts = text.split()
                command = parts[0].lower() if parts else ""
                if command in {"/kick", "/ban", "/unban", "/mod", "/unmod"}:
                    self._run_input_command(text)
                    self.message_entry.delete(0, "end")
                    return
            if text.startswith("/") and not self.is_hosting:
                self.client.send_chat(text)
                self.message_entry.delete(0, "end")
                return
            if text.startswith("/") and self.is_hosting and self.server:
                # Game commands such as /pong are handled by the server.
                self.client.send_chat(text)
                self.message_entry.delete(0, "end")
                return
            if len(text) > MAX_MESSAGE_LENGTH:
                messagebox.showwarning(
                    "Message Too Long",
                    f"Please keep messages under {MAX_MESSAGE_LENGTH} characters.",
                )
                return
            self.client.send_chat(text)
            self.message_entry.delete(0, "end")
        except Exception as exc:
            messagebox.showerror("Send Failed", str(exc))

    def _run_input_command(self, text: str) -> None:
        try:
            parts = shlex.split(text)
        except ValueError:
            parts = text.split()
        if not parts:
            raise RuntimeError("Command is required.")
        command = parts[0].lower()
        target_name = " ".join(parts[1:]).strip()
        if command not in {"/kick", "/ban", "/unban", "/mod", "/unmod"}:
            raise RuntimeError(
                "Unknown command. Use /kick NAME, /kick POSTER-ID, /ban NAME, /ban POSTER-ID, /unban NAME, /mod NAME, or /unmod NAME."
            )
        if not self.is_hosting or not self.server:
            raise RuntimeError("Only the room host can use moderation commands.")
        if not target_name:
            raise RuntimeError(f"{command} requires a participant name or anonymous ID.")
        local_name = (self.name_var.get().strip() or "User")[:MAX_NAME_LENGTH].lower()
        if command in {"/kick", "/ban"} and target_name.lower() == local_name:
            if command == "/kick":
                raise RuntimeError("Use Disconnect if you want to close your own session.")
            raise RuntimeError("Banning yourself would shut down your own access.")
        if command == "/kick":
            action = self.server.kick_user
            verb = "kicked"
        elif command == "/ban":
            action = self.server.ban_user
            verb = "banned"
        elif command == "/unban":
            action = self.server.unban_user
            verb = "unbanned"
        elif command == "/mod":
            action = self.server.promote_user
            verb = "promoted"
        else:
            action = self.server.demote_user
            verb = "demoted"
        if not action(target_name):
            if command in {"/mod", "/unmod"}:
                raise RuntimeError("That participant is no longer connected or already has that role.")
            if command == "/unban":
                raise RuntimeError("That ban entry is no longer present.")
            raise RuntimeError("That participant or anonymous ID is no longer connected.")
        self._append_chat(f"[{now_stamp()}] * Host {verb} {target_name}")

    def send_file(self) -> None:
        if not self.client or not self.connected:
            messagebox.showinfo("Not Connected", "Host or join a room before sending files.")
            return
        path = filedialog.askopenfilename(title="Choose a file to send")
        if not path:
            return
        try:
            self.client.send_file(Path(path))
            self.status_var.set(f"Sent file: {Path(path).name}")
        except Exception as exc:
            messagebox.showerror("File Transfer Failed", str(exc))

    def send_image(self) -> None:
        if not self.client or not self.connected:
            messagebox.showinfo("Not Connected", "Host or join a room before sending images.")
            return
        path = filedialog.askopenfilename(title="Choose an image to send", filetypes=IMAGE_FILE_TYPES)
        if not path:
            return
        try:
            self.client.send_image(Path(path))
            self.status_var.set(f"Sent image: {Path(path).name}")
        except Exception as exc:
            messagebox.showerror("Image Send Failed", str(exc))

    def disconnect(self) -> None:
        self.host_schedule = None
        if self.client:
            self.client.disconnect()
            self.client = None
        self._safe_stop_server()
        self.connected = False
        self.is_hosting = False
        self.moderation_path = None
        self.close_room_game_window()
        self.game_window_token = None
        self._update_roster([])
        self.status_var.set("Disconnected")
        self._update_admin_controls()
        self._best_effort_memory_scrub()

    def _check_host_schedule(self) -> None:
        try:
            schedule = self.host_schedule
            if schedule:
                now = datetime.now()
                if now >= schedule["end_at"]:
                    if self.connected:
                        self._append_chat(f"[{now_stamp()}] * Host access window ended. Room closed automatically.")
                    self.disconnect()
                    self.status_var.set("Scheduled room closed")
                elif not self.connected and now >= schedule["start_at"]:
                    try:
                        self._start_host_session(schedule)
                        self._append_chat(
                            f"[{now_stamp()}] * Scheduled room is now open until {schedule['end_at'].strftime('%Y-%m-%d %H:%M')}"
                        )
                    except Exception as exc:
                        self.host_schedule = None
                        self.is_hosting = False
                        self.status_var.set("Scheduled host failed")
                        messagebox.showerror("Scheduled Host Failed", f"Could not start scheduled room:\n{exc}")
        finally:
            self.root.after(1000, self._check_host_schedule)

    def _safe_stop_server(self) -> None:
        if self.server:
            self.server.stop()
            self.server = None

    def on_close(self) -> None:
        try:
            self.disconnect()
        except Exception:
            traceback.print_exc()
        self.root.destroy()


def main() -> None:
    APP_DIR.mkdir(parents=True, exist_ok=True)
    try:
        root = tk.Tk()
    except tk.TclError as exc:
        raise SystemExit(f"Could not start the desktop UI: {exc}") from exc
    style = ttk.Style()
    if "vista" in style.theme_names():
        style.theme_use("vista")
    app = ChatApp(root)
    app._append_chat(
        "Encrypted Chat (ERTC) ready.\n"
        "If you host, share your IP address, port, and room password with the people joining."
    )
    root.mainloop()


if __name__ == "__main__":
    main()
