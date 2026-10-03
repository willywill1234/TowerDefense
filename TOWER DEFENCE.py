"""
PIXEL PATH DEFENSE
A tower defense game for ONE or TWO players on SEPARATE COMPUTERS, built with
pygame. No image files needed - all visuals are drawn in code.

  - Play solo, or over a network: one player Hosts, the other Joins using the
    host's IP address (same Wi-Fi/LAN is easiest; for internet play the host
    forwards the port on their router).
  - Both players see the same battlefield and share gold/lives - build towers
    together in real time.
  - 4 tower types, 7 enemy types, random upgrade cards after every wave, and
    automatic saving of the host's progress.

Run with:  python game.py
Requires:  pygame   (pip install pygame)   -- networking uses only the
           Python standard library (socket/threading), nothing else to install.

CONTROLS (same for both players, each on their own computer):
  1 / 2 / 3 / 4   - select tower type (Cannon / Sniper / Frost / Mortar)
  Left click      - place the selected tower on an empty grass tile,
                    or click an existing tower to inspect/select it
  U               - upgrade the currently selected tower (costs gold)
  SPACE           - start the next wave
  ESC             - deselect the inspected tower

NETWORKING NOTES
  - The host listens on TCP port 5555. Only one Join-er can connect.
  - "Host Game" works immediately for LAN play (same Wi-Fi/router). For two
    computers on different networks, the host needs to forward TCP port 5555
    to their machine and share their public IP.
  - The host's game is authoritative and is what gets auto-saved; the joining
    player's screen mirrors it live.
"""

import pygame
import json
import os
import random
import math
import sys
import time
import socket
import threading
import queue
import itertools

# --------------------------------------------------------------------------
# CONSTANTS
# --------------------------------------------------------------------------
GRID = 40
TOPBAR_H = 56
COLS = 19
ROWS = 14
PLAY_W = COLS * GRID
PLAY_H = ROWS * GRID
SIDEBAR_W = 250
WIDTH = PLAY_W + SIDEBAR_W
HEIGHT = TOPBAR_H + PLAY_H
FPS = 60

DEFAULT_PORT = 5555

SAVE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "td_save.json")
AUTOSAVE_INTERVAL = 20  # seconds, periodic autosave while playing (host only)

# ---- palette -----------------------------------------------------------
BG = (18, 20, 26)
SIDEBAR_TOP = (30, 33, 43)
SIDEBAR_BOTTOM = (19, 21, 28)
TOPBAR_TOP = (36, 40, 52)
TOPBAR_BOTTOM = (22, 24, 32)
WHITE = (240, 240, 245)
GREY = (150, 150, 162)
DIM = (105, 108, 120)
GOLD_COLOR = (247, 197, 72)
RED = (224, 90, 90)
GREEN = (98, 205, 130)
BLUE = (86, 156, 232)
BLACK = (12, 12, 15)
CARD_BG = (42, 46, 60)
CARD_BORDER = (96, 101, 122)
NET_COLOR = (120, 200, 255)

pygame.init()
pygame.display.set_caption("Pixel Path Defense - Online Co-op")
SCREEN = pygame.display.set_mode((WIDTH, HEIGHT))
CLOCK = pygame.time.Clock()

FONT_S = pygame.font.SysFont("arial", 13)
FONT_M = pygame.font.SysFont("arial", 18)
FONT_L = pygame.font.SysFont("arial", 26, bold=True)
FONT_XL = pygame.font.SysFont("arial", 40, bold=True)

# --------------------------------------------------------------------------
# SMALL DRAWING HELPERS
# --------------------------------------------------------------------------
def darken(color, factor):
    return tuple(max(0, int(c * factor)) for c in color)


def lighten(color, factor):
    return tuple(min(255, int(c + (255 - c) * factor)) for c in color)


def lerp_color(c1, c2, t):
    t = max(0.0, min(1.0, t))
    return tuple(int(c1[i] + (c2[i] - c1[i]) * t) for i in range(3))


def rotate_points(points, angle):
    ca, sa = math.cos(angle), math.sin(angle)
    return [(px * ca - py * sa, px * sa + py * ca) for px, py in points]


def hexagon_points(r):
    return [(r * math.cos(math.pi / 6 + i * math.pi / 3),
              r * math.sin(math.pi / 6 + i * math.pi / 3)) for i in range(6)]


def star_points(r_outer, r_inner, spikes):
    pts = []
    for i in range(spikes * 2):
        ang = math.pi * i / spikes
        r = r_outer if i % 2 == 0 else r_inner
        pts.append((r * math.cos(ang), r * math.sin(ang)))
    return pts


def draw_vgradient(surf, rect, top_color, bottom_color):
    x, y, w, h = rect
    h = max(1, h)
    for i in range(h):
        t = i / h
        pygame.draw.line(surf, lerp_color(top_color, bottom_color, t), (x, y + i), (x + w, y + i))


def draw_glow_circle(surf, center, radius, color, alpha):
    r = max(1, int(radius))
    s = pygame.Surface((r * 2 + 2, r * 2 + 2), pygame.SRCALPHA)
    pygame.draw.circle(s, (*color, alpha), (r + 1, r + 1), r)
    surf.blit(s, (center[0] - r - 1, center[1] - r - 1))


def draw_ring(surf, center, radius, color, alpha, width=3):
    r = max(1, int(radius))
    s = pygame.Surface((r * 2 + 4, r * 2 + 4), pygame.SRCALPHA)
    pygame.draw.circle(s, (*color, max(0, min(255, alpha))), (r + 2, r + 2), r, width)
    surf.blit(s, (center[0] - r - 2, center[1] - r - 2))


def draw_dashed_circle(surf, center, radius, color, dash_deg=10, gap_deg=8, width=2):
    total = dash_deg + gap_deg
    steps = max(8, int(360 / total))
    for i in range(steps):
        a0 = math.radians(i * total)
        a1 = a0 + math.radians(dash_deg)
        x0, y0 = center[0] + radius * math.cos(a0), center[1] + radius * math.sin(a0)
        x1, y1 = center[0] + radius * math.cos(a1), center[1] + radius * math.sin(a1)
        pygame.draw.line(surf, color, (x0, y0), (x1, y1), width)


def draw_health_bar(surf, cx, top_y, w, h, ratio):
    x = int(cx - w / 2)
    y = int(top_y)
    bg_rect = pygame.Rect(x, y, w, h)
    pygame.draw.rect(surf, (18, 18, 22), bg_rect, border_radius=3)
    if ratio > 0:
        fill_w = max(0, int((w - 2) * ratio))
        color = lerp_color((224, 80, 80), (110, 215, 130), ratio)
        pygame.draw.rect(surf, color, (x + 1, y + 1, fill_w, h - 2), border_radius=2)
    pygame.draw.rect(surf, (8, 8, 10), bg_rect, 1, border_radius=3)


def draw_button(surf, rect, text, enabled=True, active=False, icon=None):
    color = CARD_BG if not active else (58, 96, 140)
    if not enabled:
        color = (32, 34, 40)
    pygame.draw.rect(surf, darken(color, 0.75), rect.move(0, 2), border_radius=8)
    pygame.draw.rect(surf, color, rect, border_radius=8)
    pygame.draw.rect(surf, CARD_BORDER if enabled else (55, 57, 64), rect, 2, border_radius=8)
    text_x = rect.x + 12
    if icon:
        icon(surf, (rect.x + 22, rect.centery))
        text_x = rect.x + 42
    txt = FONT_S.render(text, True, WHITE if enabled else GREY)
    surf.blit(txt, (text_x, rect.centery - txt.get_height() / 2))


# --------------------------------------------------------------------------
# PATH
# --------------------------------------------------------------------------
PATH_GRID = [
    (-1, 6), (4, 6), (4, 2), (9, 2), (9, 10), (14, 10), (14, 4), (COLS, 4)
]


def grid_to_px(gx, gy):
    return gx * GRID + GRID / 2, TOPBAR_H + gy * GRID + GRID / 2


PATH_POINTS = [grid_to_px(gx, gy) for gx, gy in PATH_GRID]
PATH_POINTS_LOCAL = [(x, y - TOPBAR_H) for x, y in PATH_POINTS]


def compute_blocked_cells():
    blocked = set()
    for (x1, y1), (x2, y2) in zip(PATH_GRID, PATH_GRID[1:]):
        if x1 == x2:
            step = 1 if y2 >= y1 else -1
            for y in range(y1, y2 + step, step):
                blocked.add((x1, y))
        else:
            step = 1 if x2 >= x1 else -1
            for x in range(x1, x2 + step, step):
                blocked.add((x, y1))
    return blocked


BLOCKED_CELLS = compute_blocked_cells()


def draw_road(surf, points, width, edge_color, fill_color, dash_color):
    for i in range(len(points) - 1):
        pygame.draw.line(surf, edge_color, points[i], points[i + 1], width)
    for p in points:
        pygame.draw.circle(surf, edge_color, (int(p[0]), int(p[1])), width // 2)

    inner_w = max(6, width - 14)
    for i in range(len(points) - 1):
        pygame.draw.line(surf, fill_color, points[i], points[i + 1], inner_w)
    for p in points:
        pygame.draw.circle(surf, fill_color, (int(p[0]), int(p[1])), inner_w // 2)

    for i in range(len(points) - 1):
        x1, y1 = points[i]
        x2, y2 = points[i + 1]
        dist = math.hypot(x2 - x1, y2 - y1)
        if dist < 1:
            continue
        steps = max(1, int(dist // 22))
        for s in range(steps):
            t = (s + 0.5) / steps
            if s % 2 == 0:
                continue
            x, y = x1 + (x2 - x1) * t, y1 + (y2 - y1) * t
            pygame.draw.circle(surf, dash_color, (int(x), int(y)), 3)


def build_background():
    surf = pygame.Surface((PLAY_W, PLAY_H))
    rng = random.Random(20240521)
    c1 = (52, 96, 49)
    c2 = (58, 104, 54)
    for gx in range(COLS):
        for gy in range(ROWS):
            color = c1 if (gx + gy) % 2 == 0 else c2
            pygame.draw.rect(surf, color, (gx * GRID, gy * GRID, GRID, GRID))

    for _ in range(1000):
        x = rng.randint(0, PLAY_W - 1)
        y = rng.randint(0, PLAY_H - 1)
        shade = rng.choice([(42, 80, 40), (70, 122, 62), (38, 72, 36)])
        length = rng.randint(2, 5)
        lean = rng.uniform(-0.4, 0.4)
        pygame.draw.line(surf, shade, (x, y), (x + lean * length, y - length), 1)

    draw_road(surf, PATH_POINTS_LOCAL, GRID + 16, (78, 58, 38), (146, 116, 74), (182, 152, 100))

    placed, attempts = 0, 0
    while placed < 50 and attempts < 3000:
        attempts += 1
        x = rng.randint(12, PLAY_W - 12)
        y = rng.randint(12, PLAY_H - 12)
        gx, gy = x // GRID, y // GRID
        if (gx, gy) in BLOCKED_CELLS:
            continue
        if rng.random() < 0.45:
            r = rng.randint(4, 7)
            pygame.draw.circle(surf, (100, 98, 90), (x, y), r)
            pygame.draw.circle(surf, (72, 70, 64), (x, y), r, 1)
            pygame.draw.circle(surf, (128, 126, 118), (x - 2, y - 2), max(1, r - 4))
        else:
            r = rng.randint(6, 9)
            pygame.draw.circle(surf, (34, 84, 40), (x, y), r)
            pygame.draw.circle(surf, (30, 70, 34), (x, y), r, 1)
            pygame.draw.circle(surf, (52, 112, 56), (x - 2, y - 3), max(2, r - 4))
        placed += 1

    return surf


BACKGROUND_SURF = build_background()

# --------------------------------------------------------------------------
# ENEMY / TOWER DEFINITIONS
# --------------------------------------------------------------------------
ENEMY_TYPES = {
    "normal":         {"hp": 40,  "speed": 1.7,  "reward": 10,  "color": (224, 92, 92),   "radius": 13},
    "fast":           {"hp": 22,  "speed": 2.9,  "reward": 8,   "color": (247, 205, 70),  "radius": 10},
    "tank":           {"hp": 130, "speed": 1.0,  "reward": 22,  "color": (150, 105, 200), "radius": 16},
    "boss":           {"hp": 600, "speed": 0.85, "reward": 120, "color": (70, 40, 90),    "radius": 24},
    "swarm":          {"hp": 12,  "speed": 2.3,  "reward": 4,   "color": (150, 220, 120), "radius": 7},
    "shielded":       {"hp": 55,  "speed": 1.2,  "reward": 20,  "color": (150, 160, 170), "radius": 15, "shield": 45},
    "splitter":       {"hp": 65,  "speed": 1.35, "reward": 16,  "color": (235, 140, 60),  "radius": 15},
    "splitter_child": {"hp": 18,  "speed": 1.8,  "reward": 5,   "color": (245, 175, 110), "radius": 9},
}

TOWER_TYPES = {
    "cannon": {"cost": 50,  "range": 110, "damage": 12, "fire_rate": 1.3,
               "color": (76, 140, 214), "proj_color": (170, 210, 255), "flash": 0.09,
               "splash": 0, "slow": None},
    "sniper": {"cost": 100, "range": 220, "damage": 35, "fire_rate": 0.6,
               "color": (86, 180, 120), "proj_color": (190, 255, 200), "flash": 0.10,
               "splash": 0, "slow": None},
    "frost":  {"cost": 70,  "range": 100, "damage": 5,  "fire_rate": 1.1,
               "color": (130, 195, 232), "proj_color": (205, 235, 250), "flash": 0.08,
               "splash": 0, "slow": (0.5, 1.4)},
    "mortar": {"cost": 140, "range": 150, "damage": 45, "fire_rate": 0.35,
               "color": (128, 122, 96), "proj_color": (255, 170, 90), "flash": 0.15,
               "splash": 45, "slow": None},
}
TOWER_KIND_LIST = ["cannon", "sniper", "frost", "mortar"]

UPGRADE_TYPES = [
    {"id": "damage", "name": "Damage Boost", "desc": "+20% damage on all towers",
     "apply": lambda s: s.update(dmg_mult=s["dmg_mult"] * 1.20)},
    {"id": "range", "name": "Range Extender", "desc": "+15% range on all towers",
     "apply": lambda s: s.update(range_mult=s["range_mult"] * 1.15)},
    {"id": "firerate", "name": "Rapid Fire", "desc": "+15% fire rate on all towers",
     "apply": lambda s: s.update(firerate_mult=s["firerate_mult"] * 1.15)},
    {"id": "gold", "name": "Gold Rush", "desc": "Instantly gain 60 gold",
     "apply": lambda s: s.update(gold=s["gold"] + 60)},
    {"id": "life", "name": "Fortify", "desc": "+2 lives",
     "apply": lambda s: s.update(lives=s["lives"] + 2)},
    {"id": "interest", "name": "Investor", "desc": "+10% gold from kills",
     "apply": lambda s: s.update(gold_mult=s["gold_mult"] * 1.10)},
    {"id": "splash", "name": "Splash Rounds", "desc": "+8 splash damage radius",
     "apply": lambda s: s.update(splash_radius=s["splash_radius"] + 8)},
    {"id": "crit", "name": "Critical Strikes", "desc": "+8% chance to deal double damage",
     "apply": lambda s: s.update(crit_chance=min(0.75, s["crit_chance"] + 0.08))},
]
UPGRADE_BY_ID = {u["id"]: u for u in UPGRADE_TYPES}


def default_state():
    return {
        "wave": 1,
        "gold": 150,
        "lives": 20,
        "best_wave": 0,
        "dmg_mult": 1.0,
        "range_mult": 1.0,
        "firerate_mult": 1.0,
        "gold_mult": 1.0,
        "splash_radius": 0.0,
        "crit_chance": 0.0,
        "towers": [],
    }


# --------------------------------------------------------------------------
# SAVE / LOAD  (host only - the joining player's game is a mirror, not a file)
# --------------------------------------------------------------------------
def save_game(state, silent=True):
    try:
        tmp = SAVE_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump(state, f, indent=2)
        os.replace(tmp, SAVE_FILE)
        if not silent:
            print("Game saved.")
    except Exception as e:
        print(f"[warning] could not save game: {e}")


def load_game():
    if os.path.exists(SAVE_FILE):
        try:
            with open(SAVE_FILE, "r") as f:
                data = json.load(f)
            base = default_state()
            base.update(data)
            return base
        except Exception as e:
            print(f"[warning] could not load save file: {e}")
    return None


def has_save():
    return os.path.exists(SAVE_FILE)


# --------------------------------------------------------------------------
# NETWORKING
# --------------------------------------------------------------------------
def get_local_ip():
    """Best-effort discovery of this machine's LAN IP (no data is actually sent)."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
    except Exception:
        ip = "127.0.0.1"
    finally:
        s.close()
    return ip


class NetworkServer:
    """Runs on the HOST's machine. Accepts exactly one Player 2 connection,
    receives their commands, and broadcasts game-state snapshots to them."""

    def __init__(self, port=DEFAULT_PORT):
        self.port = port
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sock.bind(("0.0.0.0", port))
        self.sock.listen(1)
        self.sock.settimeout(0.5)
        self.conn = None
        self.addr = None
        self.connected = False
        self.incoming = queue.Queue()
        self._stop = False
        threading.Thread(target=self._accept_loop, daemon=True).start()

    def _accept_loop(self):
        while not self._stop and not self.connected:
            try:
                conn, addr = self.sock.accept()
            except socket.timeout:
                continue
            except OSError:
                return
            self.conn = conn
            self.addr = addr
            self.connected = True
            threading.Thread(target=self._recv_loop, daemon=True).start()
            return

    def _recv_loop(self):
        buf = b""
        while not self._stop:
            try:
                data = self.conn.recv(4096)
            except OSError:
                break
            if not data:
                break
            buf += data
            while b"\n" in buf:
                line, buf = buf.split(b"\n", 1)
                if line.strip():
                    try:
                        self.incoming.put(json.loads(line.decode("utf-8")))
                    except Exception:
                        pass
        self.connected = False

    def poll_commands(self):
        cmds = []
        while not self.incoming.empty():
            try:
                cmds.append(self.incoming.get_nowait())
            except queue.Empty:
                break
        return cmds

    def broadcast(self, state):
        if not self.connected or not self.conn:
            return
        try:
            self.conn.sendall((json.dumps(state) + "\n").encode("utf-8"))
        except OSError:
            self.connected = False

    def close(self):
        self._stop = True
        self.connected = False
        try:
            self.sock.close()
        except OSError:
            pass
        if self.conn:
            try:
                self.conn.close()
            except OSError:
                pass


class NetworkClient:
    """Runs on the JOINING player's machine. Connects to the host, sends
    command messages, and keeps the most recent state snapshot received."""

    def __init__(self, host, port=DEFAULT_PORT, timeout=5):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.settimeout(timeout)
        self.sock.connect((host, port))
        self.sock.settimeout(None)
        self.connected = True
        self.latest_state = None
        self.lock = threading.Lock()
        self._stop = False
        threading.Thread(target=self._recv_loop, daemon=True).start()

    def _recv_loop(self):
        buf = b""
        while not self._stop:
            try:
                data = self.sock.recv(65536)
            except OSError:
                break
            if not data:
                break
            buf += data
            while b"\n" in buf:
                line, buf = buf.split(b"\n", 1)
                if line.strip():
                    try:
                        msg = json.loads(line.decode("utf-8"))
                        with self.lock:
                            self.latest_state = msg
                    except Exception:
                        pass
        self.connected = False

    def get_state(self):
        with self.lock:
            return self.latest_state

    def send(self, cmd):
        try:
            self.sock.sendall((json.dumps(cmd) + "\n").encode("utf-8"))
        except OSError:
            self.connected = False

    def close(self):
        self._stop = True
        self.connected = False
        try:
            self.sock.close()
        except OSError:
            pass


# --------------------------------------------------------------------------
# PARTICLES
# --------------------------------------------------------------------------
class Particle:
    def __init__(self, x, y, color, speed_range=(50, 170), life=0.5, radius=4):
        ang = random.uniform(0, math.tau)
        spd = random.uniform(*speed_range)
        self.x, self.y = x, y
        self.vx, self.vy = math.cos(ang) * spd, math.sin(ang) * spd
        self.life = life
        self.max_life = life
        self.color = color
        self.radius = radius

    def update(self, dt):
        self.x += self.vx * dt
        self.y += self.vy * dt
        self.vx *= 0.90
        self.vy *= 0.90
        self.life -= dt
        return self.life > 0

    def draw(self, surf):
        t = max(0.0, self.life / self.max_life)
        r = max(1, int(self.radius * t))
        draw_glow_circle(surf, (self.x, self.y), r, self.color, int(230 * t))


def spawn_burst(particles, x, y, color, count=14):
    for _ in range(count):
        particles.append(Particle(x, y, color))


# --------------------------------------------------------------------------
# GAME OBJECTS
# --------------------------------------------------------------------------
_enemy_id_seq = itertools.count(1)


class Enemy:
    def __init__(self, kind, wave, start_index=0, start_pos=None):
        base = ENEMY_TYPES[kind]
        scale = 1 + (wave - 1) * 0.14
        self.id = next(_enemy_id_seq)
        self.kind = kind
        self.max_hp = base["hp"] * scale
        self.hp = self.max_hp
        self.speed = base["speed"]
        self.reward = base["reward"]
        self.color = base["color"]
        self.radius = base["radius"]
        self.path_index = start_index
        self.x, self.y = start_pos if start_pos else PATH_POINTS[0]
        self.alive = True
        self.reached_end = False
        self.angle = 0.0
        self.age = 0.0
        self.trail = []
        self.slow_mult = 1.0
        self.slow_timer = 0.0
        self.max_shield = base.get("shield", 0) * scale
        self.shield_hp = self.max_shield

    def apply_slow(self, mult, duration):
        self.slow_mult = min(self.slow_mult, mult) if self.slow_timer > 0 else mult
        self.slow_timer = max(self.slow_timer, duration)

    def update(self, dt):
        self.age += dt
        if self.slow_timer > 0:
            self.slow_timer -= dt
            if self.slow_timer <= 0:
                self.slow_mult = 1.0
        if self.path_index >= len(PATH_POINTS) - 1:
            self.reached_end = True
            self.alive = False
            return
        tx, ty = PATH_POINTS[self.path_index + 1]
        dx, dy = tx - self.x, ty - self.y
        dist = math.hypot(dx, dy)
        if dist > 0.001:
            self.angle = math.atan2(dy, dx)
        if self.kind == "fast":
            self.trail.append((self.x, self.y))
            if len(self.trail) > 6:
                self.trail.pop(0)
        move = self.speed * self.slow_mult * dt * 60
        if dist < move:
            self.path_index += 1
        else:
            self.x += dx / dist * move
            self.y += dy / dist * move

    def take_damage(self, dmg):
        if self.kind == "shielded" and self.shield_hp > 0:
            if dmg <= self.shield_hp:
                self.shield_hp -= dmg
                return
            dmg -= self.shield_hp
            self.shield_hp = 0
        self.hp -= dmg
        if self.hp <= 0:
            self.alive = False

    # ---- drawing ----
    def draw(self, surf):
        if self.kind == "normal":
            self._draw_normal(surf)
        elif self.kind == "fast":
            self._draw_fast(surf)
        elif self.kind == "tank":
            self._draw_tank(surf)
        elif self.kind == "boss":
            self._draw_boss(surf)
        elif self.kind == "swarm":
            self._draw_swarm(surf)
        elif self.kind == "shielded":
            self._draw_shielded(surf)
        else:  # splitter / splitter_child
            self._draw_splitter(surf)

        if self.slow_timer > 0:
            draw_glow_circle(surf, (self.x, self.y), self.radius + 5, (150, 215, 255), 100)
        if self.kind == "shielded" and self.shield_hp > 0 and self.max_shield > 0:
            draw_ring(surf, (self.x, self.y), self.radius + 6, (120, 220, 255),
                      int(70 + 150 * (self.shield_hp / self.max_shield)))

        bar_w = self.radius * 2 + 6
        ratio = self.hp / self.max_hp if self.max_hp > 0 else 0
        draw_health_bar(surf, self.x, self.y - self.radius - 12, bar_w, 6, ratio)

    def _draw_normal(self, surf):
        bob = math.sin(self.age * 9) * 2
        cx, cy = self.x, self.y + bob
        pygame.draw.circle(surf, darken(self.color, 0.55), (int(cx), int(cy)), self.radius + 2)
        pygame.draw.circle(surf, self.color, (int(cx), int(cy)), self.radius)
        pygame.draw.circle(surf, lighten(self.color, 0.35), (int(cx - 4), int(cy - 4)), max(2, self.radius // 3))
        eye_off = self.radius * 0.42
        for sgn in (-1, 1):
            ex, ey = cx + sgn * eye_off, cy - 2
            pygame.draw.circle(surf, WHITE, (int(ex), int(ey)), 3)
            pygame.draw.circle(surf, BLACK, (int(ex + sgn), int(ey)), 1)

    def _draw_fast(self, surf):
        for i, (tx, ty) in enumerate(self.trail):
            t = (i + 1) / max(1, len(self.trail))
            r = max(1, self.radius * 0.55 * t)
            draw_glow_circle(surf, (tx, ty), r, self.color, int(110 * t))
        local_outer = [(self.radius * 1.4, 0), (-self.radius * 0.9, self.radius * 0.85),
                       (-self.radius * 0.35, 0), (-self.radius * 0.9, -self.radius * 0.85)]
        outer = [(self.x + px, self.y + py) for px, py in rotate_points(local_outer, self.angle)]
        pygame.draw.polygon(surf, darken(self.color, 0.55), outer)
        local_inner = [(px * 0.75, py * 0.75) for px, py in local_outer]
        inner = [(self.x + px, self.y + py) for px, py in rotate_points(local_inner, self.angle)]
        pygame.draw.polygon(surf, self.color, inner)

    def _draw_tank(self, surf):
        pts_outer = [(self.x + px, self.y + py)
                     for px, py in rotate_points(hexagon_points(self.radius + 2), self.angle)]
        pts_inner = [(self.x + px, self.y + py)
                     for px, py in rotate_points(hexagon_points(self.radius - 2), self.angle)]
        pygame.draw.polygon(surf, darken(self.color, 0.5), pts_outer)
        pygame.draw.polygon(surf, self.color, pts_inner)
        pygame.draw.polygon(surf, darken(self.color, 0.7), pts_inner, 2)
        for px, py in pts_inner:
            pygame.draw.circle(surf, darken(self.color, 0.4), (int(px), int(py)), 2)

    def _draw_boss(self, surf):
        spin = self.age * 0.6
        spikes = [(self.x + px, self.y + py)
                  for px, py in rotate_points(star_points(self.radius + 8, self.radius - 4, 8), spin)]
        pygame.draw.polygon(surf, darken(self.color, 0.6), spikes)
        pygame.draw.circle(surf, self.color, (int(self.x), int(self.y)), self.radius)
        pygame.draw.circle(surf, darken(self.color, 0.5), (int(self.x), int(self.y)), self.radius, 3)
        eye_off = self.radius * 0.4
        for sgn in (-1, 1):
            ex, ey = self.x + sgn * eye_off, self.y - 3
            draw_glow_circle(surf, (ex, ey), 6, (255, 60, 60), 160)
            pygame.draw.circle(surf, (255, 90, 90), (int(ex), int(ey)), 3)

    def _draw_swarm(self, surf):
        wig = math.sin(self.age * 20) * 1.5
        cx, cy = self.x + wig, self.y
        pygame.draw.circle(surf, darken(self.color, 0.6), (int(cx), int(cy)), self.radius + 1)
        pygame.draw.circle(surf, self.color, (int(cx), int(cy)), self.radius)
        for sgn in (-1, 1):
            pygame.draw.line(surf, darken(self.color, 0.5), (cx, cy),
                              (cx + sgn * self.radius, cy + self.radius), 1)
            pygame.draw.circle(surf, BLACK, (int(cx + sgn * 3), int(cy - 2)), 1)

    def _draw_shielded(self, surf):
        pts_outer = [(self.x + px, self.y + py)
                     for px, py in rotate_points(hexagon_points(self.radius + 2), self.angle)]
        pts_inner = [(self.x + px, self.y + py)
                     for px, py in rotate_points(hexagon_points(self.radius - 1), self.angle)]
        pygame.draw.polygon(surf, darken(self.color, 0.5), pts_outer)
        pygame.draw.polygon(surf, self.color, pts_inner)
        pygame.draw.polygon(surf, darken(self.color, 0.7), pts_inner, 2)

    def _draw_splitter(self, surf):
        local = [(self.radius * 1.2, 0), (0, self.radius * 1.2),
                 (-self.radius * 1.2, 0), (0, -self.radius * 1.2)]
        outer = [(self.x + px, self.y + py) for px, py in rotate_points(local, self.angle)]
        pygame.draw.polygon(surf, darken(self.color, 0.55), outer)
        inner_local = [(px * 0.75, py * 0.75) for px, py in local]
        inner = [(self.x + px, self.y + py) for px, py in rotate_points(inner_local, self.angle)]
        pygame.draw.polygon(surf, self.color, inner)
        if self.kind == "splitter":
            pygame.draw.line(surf, WHITE, inner[0], inner[2], 1)
            pygame.draw.line(surf, WHITE, inner[1], inner[3], 1)


class Projectile:
    def __init__(self, x, y, target, damage, color, splash_radius, crit_chance, slow_effect=None):
        self.x, self.y = x, y
        self.target = target
        self.damage = damage
        self.color = color
        self.speed = 9
        self.splash_radius = splash_radius
        self.crit_chance = crit_chance
        self.slow_effect = slow_effect
        self.alive = True
        self.trail = []

    def update(self, enemies, particles):
        if not self.target.alive:
            self.alive = False
            return
        self.trail.append((self.x, self.y))
        if len(self.trail) > 4:
            self.trail.pop(0)
        dx, dy = self.target.x - self.x, self.target.y - self.y
        dist = math.hypot(dx, dy)
        if dist < self.speed + self.target.radius:
            dmg = self.damage
            if random.random() < self.crit_chance:
                dmg *= 2
            self.target.take_damage(dmg)
            if self.slow_effect:
                self.target.apply_slow(*self.slow_effect)
            spawn_burst(particles, self.target.x, self.target.y, self.color, count=5)
            if self.splash_radius > 0:
                for e in enemies:
                    if e is not self.target and e.alive:
                        if math.hypot(e.x - self.target.x, e.y - self.target.y) <= self.splash_radius:
                            e.take_damage(dmg * 0.5)
                            if self.slow_effect:
                                e.apply_slow(*self.slow_effect)
                spawn_burst(particles, self.target.x, self.target.y, (255, 190, 120), count=10)
            self.alive = False
        else:
            self.x += dx / dist * self.speed
            self.y += dy / dist * self.speed

    def draw(self, surf):
        for i, (tx, ty) in enumerate(self.trail):
            t = (i + 1) / max(1, len(self.trail))
            draw_glow_circle(surf, (tx, ty), max(1, 4 * t), self.color, int(140 * t))
        draw_glow_circle(surf, (self.x, self.y), 8, self.color, 90)
        pygame.draw.circle(surf, self.color, (int(self.x), int(self.y)), 4)
        pygame.draw.circle(surf, WHITE, (int(self.x), int(self.y)), 4, 1)


class ProjView:
    """Lightweight stand-in for a Projectile on the joining client, which
    only needs to draw a received (x, y, color) - it reuses Projectile.draw."""
    __slots__ = ("x", "y", "color", "trail")

    def __init__(self, x, y, color):
        self.x, self.y = x, y
        self.color = tuple(color)
        self.trail = []

    def draw(self, surf):
        Projectile.draw(self, surf)


class Tower:
    def __init__(self, gx, gy, kind, level=1):
        self.gx, self.gy = gx, gy
        self.x, self.y = grid_to_px(gx, gy)
        self.kind = kind
        self.level = level
        self.cooldown = 0.0
        self.angle = -math.pi / 2
        self.flash_timer = 0.0
        info = TOWER_TYPES[kind]
        self.base_range = info["range"]
        self.base_damage = info["damage"]
        self.base_fire_rate = info["fire_rate"]
        self.color = info["color"]
        self.proj_color = info["proj_color"]
        self.flash_dur = info["flash"]

    def stats(self, state):
        lvl_mult = 1 + (self.level - 1) * 0.35
        rng = self.base_range * state["range_mult"] * (1 + (self.level - 1) * 0.08)
        dmg = self.base_damage * state["dmg_mult"] * lvl_mult
        rate = self.base_fire_rate * state["firerate_mult"] * (1 + (self.level - 1) * 0.1)
        return rng, dmg, rate

    def upgrade_cost(self):
        return int(40 * (self.level ** 1.4))

    def update(self, dt, enemies, projectiles, state):
        self.flash_timer = max(0.0, self.flash_timer - dt)
        self.cooldown -= dt
        rng, dmg, rate = self.stats(state)
        target = None
        best_progress = -1
        for e in enemies:
            if not e.alive:
                continue
            if math.hypot(e.x - self.x, e.y - self.y) <= rng:
                if e.path_index > best_progress:
                    best_progress = e.path_index
                    target = e
        if target:
            self.angle = math.atan2(target.y - self.y, target.x - self.x)
        else:
            self.angle += dt * 0.5

        if self.cooldown > 0:
            return
        if target:
            info = TOWER_TYPES[self.kind]
            splash = info["splash"] + state["splash_radius"]
            projectiles.append(Projectile(self.x, self.y, target, dmg, self.proj_color,
                                           splash, state["crit_chance"], slow_effect=info["slow"]))
            self.cooldown = 1.0 / rate
            self.flash_timer = self.flash_dur

    def draw(self, surf, state, selected):
        rng, dmg, rate = self.stats(state)
        if selected:
            s = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
            pygame.draw.circle(s, (255, 255, 255, 30), (int(self.x), int(self.y)), int(rng))
            surf.blit(s, (0, 0))
            draw_dashed_circle(surf, (self.x, self.y), rng, WHITE)

        base_r = 18
        shadow = pygame.Surface((base_r * 2 + 10, int(base_r * 1.1) + 6), pygame.SRCALPHA)
        pygame.draw.ellipse(shadow, (0, 0, 0, 90), shadow.get_rect())
        surf.blit(shadow, (self.x - base_r - 5, self.y + base_r * 0.25))

        if self.kind == "cannon":
            pygame.draw.circle(surf, darken(self.color, 0.55), (int(self.x), int(self.y)), base_r + 3)
            pygame.draw.circle(surf, self.color, (int(self.x), int(self.y)), base_r)
            pygame.draw.circle(surf, lighten(self.color, 0.3), (int(self.x - 5), int(self.y - 6)), base_r // 3)
            pygame.draw.circle(surf, darken(self.color, 0.7), (int(self.x), int(self.y)), base_r, 2)
            barrel_len, barrel_w = 24, 11
        elif self.kind == "sniper":
            pts_outer = [(self.x + px, self.y + py) for px, py in hexagon_points(base_r + 3)]
            pts_inner = [(self.x + px, self.y + py) for px, py in hexagon_points(base_r)]
            pygame.draw.polygon(surf, darken(self.color, 0.55), pts_outer)
            pygame.draw.polygon(surf, self.color, pts_inner)
            pygame.draw.polygon(surf, darken(self.color, 0.7), pts_inner, 2)
            pygame.draw.circle(surf, lighten(self.color, 0.3), (int(self.x - 5), int(self.y - 5)), base_r // 4)
            barrel_len, barrel_w = 34, 6
        elif self.kind == "frost":
            pygame.draw.circle(surf, darken(self.color, 0.55), (int(self.x), int(self.y)), base_r + 3)
            pygame.draw.circle(surf, self.color, (int(self.x), int(self.y)), base_r)
            pygame.draw.circle(surf, lighten(self.color, 0.4), (int(self.x - 4), int(self.y - 5)), base_r // 3)
            for i in range(6):
                a = i * math.pi / 3 + self.angle * 0.15
                sx = self.x + math.cos(a) * (base_r - 3)
                sy = self.y + math.sin(a) * (base_r - 3)
                pygame.draw.circle(surf, WHITE, (int(sx), int(sy)), 2)
            barrel_len, barrel_w = 18, 8
        else:  # mortar
            pygame.draw.circle(surf, darken(self.color, 0.5), (int(self.x), int(self.y)), base_r + 5)
            pygame.draw.circle(surf, self.color, (int(self.x), int(self.y)), base_r + 2)
            pygame.draw.circle(surf, darken(self.color, 0.7), (int(self.x), int(self.y)), base_r + 2, 2)
            pygame.draw.circle(surf, lighten(self.color, 0.25), (int(self.x - 5), int(self.y - 6)), base_r // 3)
            barrel_len, barrel_w = 20, 17

        dirx, diry = math.cos(self.angle), math.sin(self.angle)
        perp = (-diry, dirx)
        tipx, tipy = self.x + dirx * barrel_len, self.y + diry * barrel_len
        half = barrel_w / 2
        p1 = (self.x + perp[0] * half, self.y + perp[1] * half)
        p2 = (self.x - perp[0] * half, self.y - perp[1] * half)
        p3 = (tipx - perp[0] * half * 0.65, tipy - perp[1] * half * 0.65)
        p4 = (tipx + perp[0] * half * 0.65, tipy + perp[1] * half * 0.65)
        pygame.draw.polygon(surf, (58, 62, 72), [p1, p2, p3, p4])
        pygame.draw.polygon(surf, (95, 100, 112), [p1, p2, p3, p4], 1)
        pygame.draw.circle(surf, (40, 42, 50), (int(tipx), int(tipy)), max(3, int(half * 0.7)))

        if self.flash_timer > 0:
            t = self.flash_timer / self.flash_dur
            draw_glow_circle(surf, (tipx, tipy), 6 + 10 * t, (255, 225, 140), int(220 * t))

        lvl_bg = pygame.Rect(0, 0, 18, 16)
        lvl_bg.center = (int(self.x), int(self.y + base_r + 10))
        pygame.draw.rect(surf, (20, 20, 24), lvl_bg, border_radius=4)
        pygame.draw.rect(surf, GOLD_COLOR, lvl_bg, 1, border_radius=4)
        lvl_txt = FONT_S.render(str(self.level), True, WHITE)
        surf.blit(lvl_txt, (lvl_bg.centerx - lvl_txt.get_width() / 2, lvl_bg.centery - lvl_txt.get_height() / 2))


# --------------------------------------------------------------------------
# WAVE GENERATION
# --------------------------------------------------------------------------
def build_wave_queue(wave_num):
    queue_ = []
    count = 6 + wave_num * 2
    for i in range(count):
        if wave_num % 5 == 0 and i == count - 1:
            queue_.append("boss")
            continue
        if wave_num >= 4 and random.random() < 0.12:
            queue_.append("splitter")
            continue
        if wave_num >= 3 and random.random() < 0.15:
            queue_.append("shielded")
            continue
        if wave_num > 2 and random.random() < 0.20:
            queue_.append("tank")
            continue
        if wave_num >= 2 and random.random() < 0.20:
            queue_.append("swarm")
            continue
        if wave_num > 1 and random.random() < 0.28:
            queue_.append("fast")
            continue
        queue_.append("normal")
    return queue_


# --------------------------------------------------------------------------
# SIDEBAR ICONS
# --------------------------------------------------------------------------
def icon_cannon(surf, center):
    x, y = center
    pygame.draw.circle(surf, darken(TOWER_TYPES["cannon"]["color"], 0.55), (x, y), 11)
    pygame.draw.circle(surf, TOWER_TYPES["cannon"]["color"], (x, y), 9)
    pygame.draw.rect(surf, (70, 74, 84), (x - 2, y - 14, 5, 12), border_radius=1)


def icon_sniper(surf, center):
    x, y = center
    pts = [(x + px, y + py) for px, py in hexagon_points(10)]
    pygame.draw.polygon(surf, darken(TOWER_TYPES["sniper"]["color"], 0.55), pts)
    pts2 = [(x + px, y + py) for px, py in hexagon_points(7)]
    pygame.draw.polygon(surf, TOWER_TYPES["sniper"]["color"], pts2)
    pygame.draw.rect(surf, (70, 74, 84), (x - 2, y - 16, 4, 14), border_radius=1)


def icon_frost(surf, center):
    x, y = center
    color = TOWER_TYPES["frost"]["color"]
    pygame.draw.circle(surf, darken(color, 0.6), (x, y), 11)
    pygame.draw.circle(surf, color, (x, y), 9)
    for ang in (0, 60, 120):
        r = math.radians(ang)
        dx, dy = math.cos(r) * 9, math.sin(r) * 9
        pygame.draw.line(surf, WHITE, (x - dx, y - dy), (x + dx, y + dy), 2)


def icon_mortar(surf, center):
    x, y = center
    color = TOWER_TYPES["mortar"]["color"]
    pygame.draw.circle(surf, darken(color, 0.55), (x, y), 12)
    pygame.draw.circle(surf, color, (x, y), 10)
    pygame.draw.rect(surf, (60, 60, 64), (x - 4, y - 14, 8, 10), border_radius=2)


TOWER_ICONS = {"cannon": icon_cannon, "sniper": icon_sniper, "frost": icon_frost, "mortar": icon_mortar}


# --------------------------------------------------------------------------
# GAME
# --------------------------------------------------------------------------
class Game:
    """
    role == 'solo'   : normal single-player, everything local (like before).
    role == 'host'   : authoritative simulation; optionally a NetworkServer
                        relays a second player's commands in and state out.
    role == 'client' : no local simulation - mirrors state received from the
                        host's NetworkServer and sends it command messages.
    """

    def __init__(self, role="solo", network=None):
        self.role = role
        self.network = network

        loaded = load_game() if role != "client" else None
        self.state = loaded if loaded else default_state()
        self.towers = [Tower(t["gx"], t["gy"], t["type"], t.get("level", 1))
                        for t in self.state["towers"]] if role != "client" else []
        self.enemies = []
        self.projectiles = []
        self.particles = []
        self.spawn_queue = []
        self.spawn_timer = 0
        self.phase = "CONNECTING" if role == "client" else "BUILD"
        self.selected_tower_type = "cannon"
        self.selected_tower = None
        self.upgrade_choices = []
        self.last_autosave = time.time()
        self.last_broadcast = 0.0
        self.message = ""
        self.message_timer = 0
        self._enemy_by_id = {}

    def is_client(self):
        return self.role == "client"

    def send_cmd(self, cmd):
        if self.network:
            self.network.send(cmd)

    # ---------------- persistence (host/solo only) ----------------
    def sync_state_towers(self):
        self.state["towers"] = [
            {"gx": t.gx, "gy": t.gy, "type": t.kind, "level": t.level} for t in self.towers
        ]

    def autosave(self, force=False, silent=True):
        if self.role == "client":
            return
        now = time.time()
        if force or now - self.last_autosave > AUTOSAVE_INTERVAL:
            self.sync_state_towers()
            save_game(self.state, silent=silent)
            self.last_autosave = now
            self.flash("Game saved")

    def flash(self, text):
        self.message = text
        self.message_timer = 90

    # ---------------- grid helpers ----------------
    def cell_at(self, mx, my):
        if mx >= PLAY_W or my < TOPBAR_H:
            return None
        gx, gy = mx // GRID, (my - TOPBAR_H) // GRID
        return int(gx), int(gy)

    def tower_at(self, gx, gy):
        for t in self.towers:
            if t.gx == gx and t.gy == gy:
                return t
        return None

    # ---------------- game flow (authoritative: solo/host) ----------------
    def start_wave(self):
        if self.phase != "BUILD":
            return
        self.spawn_queue = build_wave_queue(self.state["wave"])
        self.spawn_timer = 0
        self.phase = "WAVE"

    def complete_wave(self):
        self.state["best_wave"] = max(self.state["best_wave"], self.state["wave"])
        self.upgrade_choices = random.sample(UPGRADE_TYPES, 3)
        self.phase = "UPGRADE"
        self.autosave(force=True)

    def choose_upgrade(self, upgrade):
        upgrade["apply"](self.state)
        self.state["wave"] += 1
        self.phase = "BUILD"
        self.autosave(force=True)
        self.flash(f"Applied: {upgrade['name']}")

    def place_tower(self, gx, gy, kind=None):
        kind = kind or self.selected_tower_type
        if (gx, gy) in BLOCKED_CELLS:
            self.flash("Can't build on the path")
            return
        if not (0 <= gx < COLS and 0 <= gy < ROWS):
            return
        existing = self.tower_at(gx, gy)
        if existing:
            self.selected_tower = existing
            return
        cost = TOWER_TYPES[kind]["cost"]
        if self.state["gold"] < cost:
            self.flash("Not enough gold")
            return
        self.state["gold"] -= cost
        t = Tower(gx, gy, kind)
        self.towers.append(t)
        self.selected_tower = t
        self.autosave(force=True)

    def upgrade_tower(self, tower):
        if not tower:
            return
        cost = tower.upgrade_cost()
        if self.state["gold"] < cost:
            self.flash("Not enough gold to upgrade")
            return
        self.state["gold"] -= cost
        tower.level += 1
        self.autosave(force=True)
        self.flash("Tower upgraded!")

    def upgrade_selected_tower(self):
        self.upgrade_tower(self.selected_tower)

    def lose_life(self):
        self.state["lives"] -= 1
        if self.state["lives"] <= 0:
            self.state["lives"] = 0
            self.phase = "GAME_OVER"
            self.state["best_wave"] = max(self.state["best_wave"], self.state["wave"] - 1)
            self.autosave(force=True)

    def new_game(self):
        self.state = default_state()
        self.towers = []
        self.enemies = []
        self.projectiles = []
        self.particles = []
        self.spawn_queue = []
        self.phase = "BUILD"
        self.selected_tower = None
        self.autosave(force=True)

    # ---------------- host: apply commands received from Player 2 ----------------
    def apply_incoming_commands(self):
        if not self.network:
            return
        for cmd in self.network.poll_commands():
            try:
                kind = cmd.get("cmd")
                if kind == "click":
                    self.place_tower(cmd["gx"], cmd["gy"], kind=cmd.get("kind"))
                elif kind == "upgrade":
                    self.upgrade_selected_tower()
                elif kind == "deselect":
                    self.selected_tower = None
                elif kind == "start_wave":
                    self.start_wave()
                elif kind == "choose_upgrade" and self.phase == "UPGRADE":
                    up = UPGRADE_BY_ID.get(cmd.get("id"))
                    if up and up in self.upgrade_choices:
                        self.choose_upgrade(up)
                elif kind == "new_game":
                    self.new_game()
                elif kind == "save":
                    self.autosave(force=True, silent=False)
            except Exception as e:
                print(f"[warning] bad command from peer: {e}")

    # ---------------- host: build + send a state snapshot ----------------
    def serialize_state(self):
        s = self.state
        sel = [self.selected_tower.gx, self.selected_tower.gy] if self.selected_tower else None
        return {
            "gold": s["gold"], "lives": s["lives"], "wave": s["wave"], "best_wave": s["best_wave"],
            "dmg_mult": s["dmg_mult"], "range_mult": s["range_mult"], "firerate_mult": s["firerate_mult"],
            "gold_mult": s["gold_mult"], "splash_radius": s["splash_radius"], "crit_chance": s["crit_chance"],
            "phase": self.phase,
            "selected": sel,
            "message": self.message, "message_timer": self.message_timer,
            "towers": [{"gx": t.gx, "gy": t.gy, "kind": t.kind, "level": t.level,
                        "angle": round(t.angle, 3), "flash": round(t.flash_timer, 3)} for t in self.towers],
            "enemies": [{"id": e.id, "kind": e.kind, "x": round(e.x, 1), "y": round(e.y, 1),
                         "hp": round(e.hp, 1), "max_hp": round(e.max_hp, 1), "angle": round(e.angle, 3),
                         "shield": round(e.shield_hp, 1), "max_shield": round(e.max_shield, 1),
                         "slow": e.slow_timer > 0} for e in self.enemies],
            "projectiles": [{"x": round(p.x, 1), "y": round(p.y, 1), "color": p.color}
                             for p in self.projectiles],
            "upgrade_choices": [{"id": u["id"], "name": u["name"], "desc": u["desc"]}
                                 for u in self.upgrade_choices],
        }

    # ---------------- client: absorb a state snapshot ----------------
    def apply_remote_state(self, data):
        if data is None:
            return
        for k in ("gold", "lives", "wave", "best_wave", "dmg_mult", "range_mult",
                  "firerate_mult", "gold_mult", "splash_radius", "crit_chance"):
            self.state[k] = data[k]
        self.phase = data["phase"]
        self.message = data.get("message", "")
        self.message_timer = data.get("message_timer", 0)
        self.upgrade_choices = data.get("upgrade_choices", [])

        tower_map = {(t.gx, t.gy): t for t in self.towers}
        new_towers = []
        for td in data["towers"]:
            key = (td["gx"], td["gy"])
            t = tower_map.get(key)
            if t is None or t.kind != td["kind"]:
                t = Tower(td["gx"], td["gy"], td["kind"], td["level"])
            t.level = td["level"]
            t.angle = td["angle"]
            t.flash_timer = td["flash"]
            new_towers.append(t)
        self.towers = new_towers

        if data.get("selected"):
            sgx, sgy = data["selected"]
            self.selected_tower = next((t for t in self.towers if t.gx == sgx and t.gy == sgy), None)
        else:
            self.selected_tower = None

        incoming_ids = set()
        new_enemies = []
        for ed in data["enemies"]:
            eid = ed["id"]
            incoming_ids.add(eid)
            e = self._enemy_by_id.get(eid)
            prev_hp = e.hp if e else None
            if e is None:
                e = Enemy(ed["kind"], 1)
                e.id = eid
                self._enemy_by_id[eid] = e
            e.x, e.y = ed["x"], ed["y"]
            e.angle = ed["angle"]
            e.hp, e.max_hp = ed["hp"], ed["max_hp"]
            e.shield_hp, e.max_shield = ed.get("shield", 0), ed.get("max_shield", 0)
            e.slow_timer = 1.0 if ed.get("slow") else 0.0
            if e.kind == "fast":
                e.trail.append((e.x, e.y))
                if len(e.trail) > 6:
                    e.trail.pop(0)
            if prev_hp is not None and ed["hp"] < prev_hp - 0.01:
                spawn_burst(self.particles, e.x, e.y, e.color, count=4)
            new_enemies.append(e)

        for eid in list(self._enemy_by_id.keys()):
            if eid not in incoming_ids:
                dead = self._enemy_by_id.pop(eid)
                spawn_burst(self.particles, dead.x, dead.y, dead.color, count=14)

        self.enemies = new_enemies
        self.projectiles = [ProjView(pd["x"], pd["y"], pd["color"]) for pd in data["projectiles"]]

    # ---------------- update ----------------
    def update(self, dt):
        if self.role == "client":
            if self.network:
                self.apply_remote_state(self.network.get_state())
            self.particles = [p for p in self.particles if p.update(dt)]
            if self.message_timer > 0:
                self.message_timer -= 1
            return

        if self.role == "host":
            self.apply_incoming_commands()

        if self.phase == "WAVE":
            self.spawn_timer -= dt
            if self.spawn_queue and self.spawn_timer <= 0:
                kind = self.spawn_queue.pop(0)
                self.enemies.append(Enemy(kind, self.state["wave"]))
                self.spawn_timer = 0.25 if kind == "swarm" else 0.65

            for e in self.enemies:
                e.update(dt)
                if e.reached_end:
                    self.lose_life()

            self.enemies = [e for e in self.enemies if e.alive]

            for t in self.towers:
                t.update(dt, self.enemies, self.projectiles, self.state)

            for p in self.projectiles:
                p.update(self.enemies, self.particles)

            still_alive_after = []
            new_spawns = []
            for e in self.enemies:
                if not e.alive and not e.reached_end:
                    self.state["gold"] += int(e.reward * self.state["gold_mult"])
                    spawn_burst(self.particles, e.x, e.y, e.color, count=16)
                    if e.kind == "splitter":
                        for _ in range(2):
                            new_spawns.append(Enemy("splitter_child", self.state["wave"],
                                                     start_index=e.path_index, start_pos=(e.x, e.y)))
                else:
                    still_alive_after.append(e)
            self.enemies = still_alive_after + new_spawns
            self.projectiles = [p for p in self.projectiles if p.alive]

            if not self.spawn_queue and not self.enemies and self.phase == "WAVE":
                self.complete_wave()

            self.autosave()
        else:
            for t in self.towers:
                t.flash_timer = max(0.0, t.flash_timer - dt)

        self.particles = [p for p in self.particles if p.update(dt)]
        if self.message_timer > 0:
            self.message_timer -= 1

        if self.role == "host" and self.network:
            self.network.broadcast(self.serialize_state())

    # ---------------- drawing ----------------
    def _draw_build_ghost(self, gx, gy, kind, color):
        if not (0 <= gx < COLS and 0 <= gy < ROWS) or self.tower_at(gx, gy):
            return
        cx, cy = grid_to_px(gx, gy)
        cost = TOWER_TYPES[kind]["cost"]
        valid = (gx, gy) not in BLOCKED_CELLS and self.state["gold"] >= cost
        c = color if valid else (230, 90, 90)
        rng = TOWER_TYPES[kind]["range"] * self.state["range_mult"]
        s = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
        pygame.draw.circle(s, (*c, 25), (int(cx), int(cy)), int(rng))
        SCREEN.blit(s, (0, 0))
        draw_dashed_circle(SCREEN, (cx, cy), rng, c)
        ghost = pygame.Surface((GRID, GRID), pygame.SRCALPHA)
        pygame.draw.rect(ghost, (*c, 70), ghost.get_rect(), border_radius=6)
        pygame.draw.rect(ghost, (*c, 220), ghost.get_rect(), 2, border_radius=6)
        SCREEN.blit(ghost, (cx - GRID / 2, cy - GRID / 2))

    def draw_play_area(self):
        SCREEN.blit(BACKGROUND_SURF, (0, TOPBAR_H))
        if self.phase in ("BUILD", "WAVE"):
            mx, my = pygame.mouse.get_pos()
            cell = self.cell_at(mx, my)
            if cell:
                self._draw_build_ghost(cell[0], cell[1], self.selected_tower_type, (120, 230, 140))

    def draw_topbar(self):
        draw_vgradient(SCREEN, (0, 0, WIDTH, TOPBAR_H), TOPBAR_TOP, TOPBAR_BOTTOM)
        pygame.draw.line(SCREEN, (10, 10, 14), (0, TOPBAR_H - 1), (WIDTH, TOPBAR_H - 1), 2)
        s = self.state

        title = FONT_L.render("PIXEL PATH DEFENSE", True, WHITE)
        SCREEN.blit(title, (16, (TOPBAR_H - title.get_height()) / 2))

        stats_x = 300
        chips = [(f"{s['gold']}", "coin"), (f"{s['lives']}", "heart"),
                 (f"Wave {s['wave']}", None), (f"Best {s['best_wave']}", None)]
        for text, icon in chips:
            txt = FONT_M.render(text, True, WHITE)
            pad = 10
            icon_w = 20 if icon else 0
            chip_w = txt.get_width() + pad * 2 + icon_w
            chip_rect = pygame.Rect(stats_x, (TOPBAR_H - 30) / 2, chip_w, 30)
            pygame.draw.rect(SCREEN, darken(CARD_BG, 1.1), chip_rect, border_radius=15)
            pygame.draw.rect(SCREEN, CARD_BORDER, chip_rect, 1, border_radius=15)
            cx = chip_rect.x + pad
            if icon == "coin":
                pygame.draw.circle(SCREEN, GOLD_COLOR, (cx + 7, chip_rect.centery), 7)
                pygame.draw.circle(SCREEN, darken(GOLD_COLOR, 0.7), (cx + 7, chip_rect.centery), 7, 1)
                cx += 18
            elif icon == "heart":
                pygame.draw.circle(SCREEN, RED, (cx + 4, chip_rect.centery - 2), 4)
                pygame.draw.circle(SCREEN, RED, (cx + 10, chip_rect.centery - 2), 4)
                pygame.draw.polygon(SCREEN, RED, [(cx, chip_rect.centery), (cx + 14, chip_rect.centery),
                                                   (cx + 7, chip_rect.centery + 8)])
                cx += 20
            SCREEN.blit(txt, (cx, chip_rect.centery - txt.get_height() / 2))
            stats_x += chip_w + 12

        if self.message_timer > 0:
            m = FONT_M.render(self.message, True, GOLD_COLOR)
            SCREEN.blit(m, (WIDTH - m.get_width() - 16, (TOPBAR_H - m.get_height()) / 2))

    def sidebar_rects(self):
        x = PLAY_W + 16
        return {
            "cannon": pygame.Rect(x, TOPBAR_H + 12, SIDEBAR_W - 32, 40),
            "sniper": pygame.Rect(x, TOPBAR_H + 58, SIDEBAR_W - 32, 40),
            "frost": pygame.Rect(x, TOPBAR_H + 104, SIDEBAR_W - 32, 40),
            "mortar": pygame.Rect(x, TOPBAR_H + 150, SIDEBAR_W - 32, 40),
            "start": pygame.Rect(x, TOPBAR_H + 200, SIDEBAR_W - 32, 40),
            "upgrade_tower": pygame.Rect(x, TOPBAR_H + 514, SIDEBAR_W - 32, 36),
            "save": pygame.Rect(x, HEIGHT - 46, SIDEBAR_W - 32, 36),
        }

    def network_status_lines(self):
        if self.role == "solo":
            return "Solo game", "Not networked"
        if self.role == "host":
            ip = get_local_ip()
            if self.network and self.network.connected:
                return "Hosting - Player 2 connected", f"{ip}:{self.network.port}"
            return "Hosting - waiting for Player 2...", f"Share: {ip}:{self.network.port}"
        # client
        if self.network and self.network.connected:
            return "Joined as Player 2", "Connected to host"
        return "Joined as Player 2", "Disconnected!"

    def draw_sidebar(self):
        draw_vgradient(SCREEN, (PLAY_W, TOPBAR_H, SIDEBAR_W, PLAY_H), SIDEBAR_TOP, SIDEBAR_BOTTOM)
        pygame.draw.line(SCREEN, (10, 10, 14), (PLAY_W, TOPBAR_H), (PLAY_W, HEIGHT), 2)
        r = self.sidebar_rects()

        for kind, key in zip(TOWER_KIND_LIST, ["cannon", "sniper", "frost", "mortar"]):
            cost = TOWER_TYPES[kind]["cost"]
            draw_button(SCREEN, r[key], f"{kind.title()} (${cost}) [{TOWER_KIND_LIST.index(kind)+1}]",
                        active=self.selected_tower_type == kind, icon=TOWER_ICONS[kind])

        draw_button(SCREEN, r["start"],
                    "Start Wave" if self.phase == "BUILD" else "Wave in progress...",
                    enabled=self.phase == "BUILD")

        pygame.draw.line(SCREEN, CARD_BORDER, (PLAY_W + 16, TOPBAR_H + 250),
                          (WIDTH - 16, TOPBAR_H + 250), 1)
        label = FONT_S.render("PERMANENT UPGRADES", True, DIM)
        SCREEN.blit(label, (PLAY_W + 16, TOPBAR_H + 258))

        y = TOPBAR_H + 276
        stat_lines = [
            f"Damage x{self.state['dmg_mult']:.2f}",
            f"Range x{self.state['range_mult']:.2f}",
            f"Fire Rate x{self.state['firerate_mult']:.2f}",
            f"Gold Bonus x{self.state['gold_mult']:.2f}",
            f"Splash Radius {self.state['splash_radius']:.0f}",
            f"Crit Chance {int(self.state['crit_chance']*100)}%",
        ]
        for line in stat_lines:
            txt = FONT_S.render(line, True, GREY)
            SCREEN.blit(txt, (PLAY_W + 16, y))
            y += 15

        pygame.draw.line(SCREEN, CARD_BORDER, (PLAY_W + 16, TOPBAR_H + 374),
                          (WIDTH - 16, TOPBAR_H + 374), 1)
        net_line1, net_line2 = self.network_status_lines()
        net_label = FONT_S.render("NETWORK", True, NET_COLOR)
        SCREEN.blit(net_label, (PLAY_W + 16, TOPBAR_H + 382))
        n1 = FONT_S.render(net_line1, True, WHITE)
        n2 = FONT_S.render(net_line2, True, DIM)
        SCREEN.blit(n1, (PLAY_W + 16, TOPBAR_H + 400))
        SCREEN.blit(n2, (PLAY_W + 16, TOPBAR_H + 416))

        pygame.draw.line(SCREEN, CARD_BORDER, (PLAY_W + 16, TOPBAR_H + 438),
                          (WIDTH - 16, TOPBAR_H + 438), 1)

        if self.selected_tower:
            t = self.selected_tower
            rng, dmg, rate = t.stats(self.state)
            name_txt = FONT_M.render(f"{t.kind.title()} - Lv {t.level}", True, WHITE)
            SCREEN.blit(name_txt, (PLAY_W + 16, TOPBAR_H + 446))
            info_lines = [f"Damage: {dmg:.1f}", f"Range: {rng:.0f}", f"Fire rate: {rate:.2f}/s"]
            iy = TOPBAR_H + 470
            for line in info_lines:
                txt = FONT_S.render(line, True, GREY)
                SCREEN.blit(txt, (PLAY_W + 16, iy))
                iy += 15
            cost = t.upgrade_cost()
            draw_button(SCREEN, r["upgrade_tower"], f"Upgrade (${cost})",
                        enabled=self.state["gold"] >= cost)
        else:
            hint = FONT_S.render("Click a tower to inspect it", True, DIM)
            SCREEN.blit(hint, (PLAY_W + 16, TOPBAR_H + 446))

        draw_button(SCREEN, r["save"], "Save Now" if self.role != "client" else "Request Save")

    def draw_upgrade_screen(self):
        overlay = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
        overlay.fill((0, 0, 0, 185))
        SCREEN.blit(overlay, (0, 0))
        title = FONT_XL.render("Wave Complete! Choose an upgrade", True, WHITE)
        SCREEN.blit(title, ((WIDTH - title.get_width()) / 2, 90))

        card_w, card_h = 220, 220
        gap = 30
        total_w = card_w * 3 + gap * 2
        start_x = (WIDTH - total_w) / 2
        y = 200
        rects = []
        mx, my = pygame.mouse.get_pos()
        for i, up in enumerate(self.upgrade_choices):
            rect = pygame.Rect(start_x + i * (card_w + gap), y, card_w, card_h)
            rects.append(rect)
            hovered = rect.collidepoint(mx, my)
            draw_vgradient(SCREEN, rect, lighten(CARD_BG, 0.08) if hovered else CARD_BG,
                           darken(CARD_BG, 0.85))
            border_color = GOLD_COLOR if hovered else CARD_BORDER
            pygame.draw.rect(SCREEN, border_color, rect, 3, border_radius=10)
            name_txt = FONT_L.render(up["name"], True, WHITE)
            SCREEN.blit(name_txt, (rect.x + (card_w - name_txt.get_width()) / 2, rect.y + 24))
            words = up["desc"].split(" ")
            lines, cur = [], ""
            for w in words:
                trial = (cur + " " + w).strip()
                if FONT_M.size(trial)[0] > card_w - 24:
                    lines.append(cur)
                    cur = w
                else:
                    cur = trial
            lines.append(cur)
            dy = rect.y + 90
            for line in lines:
                t = FONT_M.render(line, True, GREY)
                SCREEN.blit(t, (rect.x + (card_w - t.get_width()) / 2, dy))
                dy += 22
        return rects

    def draw_game_over(self):
        overlay = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
        overlay.fill((0, 0, 0, 205))
        SCREEN.blit(overlay, (0, 0))
        title = FONT_XL.render("Game Over", True, RED)
        SCREEN.blit(title, ((WIDTH - title.get_width()) / 2, HEIGHT / 2 - 80))
        sub = FONT_L.render(f"You reached wave {self.state['wave']}  (Best: {self.state['best_wave']})",
                             True, WHITE)
        SCREEN.blit(sub, ((WIDTH - sub.get_width()) / 2, HEIGHT / 2 - 30))
        btn = pygame.Rect(WIDTH / 2 - 100, HEIGHT / 2 + 30, 200, 46)
        draw_button(SCREEN, btn, "New Game")
        return btn

    def draw_connecting(self):
        overlay = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
        overlay.fill((0, 0, 0, 210))
        SCREEN.blit(overlay, (0, 0))
        title = FONT_XL.render("Connected! Waiting for game data...", True, WHITE)
        SCREEN.blit(title, ((WIDTH - title.get_width()) / 2, HEIGHT / 2 - 20))

    def draw_disconnected(self):
        overlay = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
        overlay.fill((0, 0, 0, 220))
        SCREEN.blit(overlay, (0, 0))
        title = FONT_XL.render("Disconnected from host", True, RED)
        SCREEN.blit(title, ((WIDTH - title.get_width()) / 2, HEIGHT / 2 - 40))
        sub = FONT_M.render("Close this window to exit.", True, WHITE)
        SCREEN.blit(sub, ((WIDTH - sub.get_width()) / 2, HEIGHT / 2 + 10))

    def draw(self):
        SCREEN.fill(BG)
        self.draw_play_area()
        for t in self.towers:
            t.draw(SCREEN, self.state, selected=(t is self.selected_tower))
        for e in self.enemies:
            e.draw(SCREEN)
        for p in self.projectiles:
            p.draw(SCREEN)
        for p in self.particles:
            p.draw(SCREEN)
        self.draw_topbar()
        self.draw_sidebar()

        upgrade_rects = []
        gameover_btn = None
        if self.phase == "UPGRADE":
            upgrade_rects = self.draw_upgrade_screen()
        elif self.phase == "GAME_OVER":
            gameover_btn = self.draw_game_over()
        elif self.phase == "CONNECTING":
            self.draw_connecting()

        if self.role == "client" and self.network and not self.network.connected:
            self.draw_disconnected()

        pygame.display.flip()
        return upgrade_rects, gameover_btn

    # ---------------- input ----------------
    def handle_click(self, pos, upgrade_rects, gameover_btn):
        mx, my = pos
        if self.phase == "UPGRADE":
            for rect, up in zip(upgrade_rects, self.upgrade_choices):
                if rect.collidepoint(mx, my):
                    if self.is_client():
                        self.send_cmd({"cmd": "choose_upgrade", "id": up["id"]})
                    else:
                        self.choose_upgrade(up if "apply" in up else UPGRADE_BY_ID[up["id"]])
            return

        if self.phase == "GAME_OVER":
            if gameover_btn and gameover_btn.collidepoint(mx, my):
                if self.is_client():
                    self.send_cmd({"cmd": "new_game"})
                else:
                    self.new_game()
            return

        r = self.sidebar_rects()
        for kind, key in zip(TOWER_KIND_LIST, ["cannon", "sniper", "frost", "mortar"]):
            if r[key].collidepoint(mx, my):
                self.selected_tower_type = kind
                return
        if r["start"].collidepoint(mx, my):
            if self.is_client():
                self.send_cmd({"cmd": "start_wave"})
            else:
                self.start_wave()
            return
        if self.selected_tower and r["upgrade_tower"].collidepoint(mx, my):
            if self.is_client():
                self.send_cmd({"cmd": "upgrade"})
            else:
                self.upgrade_selected_tower()
            return
        if r["save"].collidepoint(mx, my):
            if self.is_client():
                self.send_cmd({"cmd": "save"})
            else:
                self.autosave(force=True, silent=False)
            return

        cell = self.cell_at(mx, my)
        if cell:
            gx, gy = cell
            if self.is_client():
                self.send_cmd({"cmd": "click", "gx": gx, "gy": gy, "kind": self.selected_tower_type})
            else:
                existing = self.tower_at(gx, gy)
                if existing:
                    self.selected_tower = existing
                else:
                    self.place_tower(gx, gy)
        else:
            if not self.is_client():
                self.selected_tower = None


# --------------------------------------------------------------------------
# LOBBY (choose Solo / Host / Join before the game starts)
# --------------------------------------------------------------------------
def draw_text_box(rect, text, active):
    pygame.draw.rect(SCREEN, (32, 34, 42), rect, border_radius=6)
    pygame.draw.rect(SCREEN, NET_COLOR if active else CARD_BORDER, rect, 2, border_radius=6)
    txt = FONT_M.render(text or " ", True, WHITE)
    SCREEN.blit(txt, (rect.x + 10, rect.centery - txt.get_height() / 2))


def run_lobby():
    state = "main"
    ip_text = ""
    error_msg = ""

    btn_w, btn_h = 320, 56
    cx = WIDTH / 2
    solo_btn = pygame.Rect(0, 0, btn_w, btn_h)
    solo_btn.center = (cx, HEIGHT / 2 - 70)
    host_btn = pygame.Rect(0, 0, btn_w, btn_h)
    host_btn.center = (cx, HEIGHT / 2)
    join_btn = pygame.Rect(0, 0, btn_w, btn_h)
    join_btn.center = (cx, HEIGHT / 2 + 70)

    ip_box = pygame.Rect(0, 0, 320, 46)
    ip_box.center = (cx, HEIGHT / 2 - 20)
    connect_btn = pygame.Rect(0, 0, 320, 50)
    connect_btn.center = (cx, HEIGHT / 2 + 50)
    back_btn = pygame.Rect(0, 0, 150, 40)
    back_btn.center = (cx, HEIGHT / 2 + 120)

    while True:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()

            if state == "main" and event.type == pygame.MOUSEBUTTONDOWN:
                if solo_btn.collidepoint(event.pos):
                    return "solo", None
                if host_btn.collidepoint(event.pos):
                    server = NetworkServer(DEFAULT_PORT)
                    return "host", server
                if join_btn.collidepoint(event.pos):
                    state = "join"
                    ip_text = ""
                    error_msg = ""

            elif state == "join":
                if event.type == pygame.KEYDOWN:
                    if event.key == pygame.K_ESCAPE:
                        state = "main"
                    elif event.key == pygame.K_BACKSPACE:
                        ip_text = ip_text[:-1]
                    elif event.key == pygame.K_RETURN:
                        error_msg = _attempt_connect(ip_text)
                        if error_msg is None:
                            client = _last_client[0]
                            return "client", client
                    else:
                        ch = event.unicode
                        if ch and (ch.isdigit() or ch in ".:") and len(ip_text) < 30:
                            ip_text += ch
                elif event.type == pygame.MOUSEBUTTONDOWN:
                    if back_btn.collidepoint(event.pos):
                        state = "main"
                    elif connect_btn.collidepoint(event.pos):
                        error_msg = _attempt_connect(ip_text)
                        if error_msg is None:
                            client = _last_client[0]
                            return "client", client

        # ---- draw ----
        SCREEN.fill(BG)
        title = FONT_XL.render("PIXEL PATH DEFENSE", True, WHITE)
        SCREEN.blit(title, ((WIDTH - title.get_width()) / 2, 90))
        sub = FONT_M.render("Play together from two computers", True, GREY)
        SCREEN.blit(sub, ((WIDTH - sub.get_width()) / 2, 140))

        if state == "main":
            draw_button(SCREEN, solo_btn, "Play Solo")
            draw_button(SCREEN, host_btn, "Host Game (2 Players)")
            draw_button(SCREEN, join_btn, "Join Game")
        else:
            label = FONT_M.render("Enter host IP address:", True, WHITE)
            SCREEN.blit(label, (ip_box.x, ip_box.y - 30))
            draw_text_box(ip_box, ip_text, True)
            draw_button(SCREEN, connect_btn, "Connect")
            draw_button(SCREEN, back_btn, "Back")
            hint = FONT_S.render("e.g. 192.168.1.42  (same Wi-Fi as the host)", True, DIM)
            SCREEN.blit(hint, (cx - hint.get_width() / 2, ip_box.bottom + 8))
            if error_msg:
                err = FONT_S.render(error_msg, True, RED)
                SCREEN.blit(err, (cx - err.get_width() / 2, back_btn.bottom + 16))

        pygame.display.flip()
        CLOCK.tick(30)


_last_client = [None]


def _attempt_connect(ip_text):
    ip_text = ip_text.strip()
    if not ip_text:
        return "Please enter an IP address."
    host_ip = ip_text
    port = DEFAULT_PORT
    if ":" in ip_text:
        host_ip, port_s = ip_text.split(":", 1)
        try:
            port = int(port_s)
        except ValueError:
            return "Invalid port number."

    connecting_txt = FONT_M.render(f"Connecting to {host_ip}:{port} ...", True, WHITE)
    SCREEN.fill(BG)
    SCREEN.blit(connecting_txt, ((WIDTH - connecting_txt.get_width()) / 2, HEIGHT / 2))
    pygame.display.flip()

    try:
        client = NetworkClient(host_ip, port, timeout=5)
        _last_client[0] = client
        return None
    except Exception as e:
        return f"Could not connect: {e}"


# --------------------------------------------------------------------------
# MAIN LOOP
# --------------------------------------------------------------------------
def main():
    role, network = run_lobby()
    game = Game(role=role, network=network)
    running = True
    while running:
        dt = CLOCK.tick(FPS) / 1000.0

        upgrade_rects, gameover_btn = game.draw()

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                if not game.is_client():
                    game.autosave(force=True, silent=False)
                if network:
                    network.close()
                running = False
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_1:
                    game.selected_tower_type = "cannon"
                elif event.key == pygame.K_2:
                    game.selected_tower_type = "sniper"
                elif event.key == pygame.K_3:
                    game.selected_tower_type = "frost"
                elif event.key == pygame.K_4:
                    game.selected_tower_type = "mortar"
                elif event.key == pygame.K_SPACE:
                    if game.is_client():
                        game.send_cmd({"cmd": "start_wave"})
                    else:
                        game.start_wave()
                elif event.key == pygame.K_u:
                    if game.is_client():
                        game.send_cmd({"cmd": "upgrade"})
                    else:
                        game.upgrade_selected_tower()
                elif event.key == pygame.K_ESCAPE:
                    if game.is_client():
                        game.send_cmd({"cmd": "deselect"})
                    else:
                        game.selected_tower = None
            elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                game.handle_click(event.pos, upgrade_rects, gameover_btn)

        game.update(dt)

    pygame.quit()
    sys.exit()


if __name__ == "__main__":
    main()