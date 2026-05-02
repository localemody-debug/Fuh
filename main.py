import discord
from discord.ext import commands
from discord import app_commands
import asyncpg
import asyncio
import aiohttp
import random
import math
import os
import hashlib
import secrets
import hmac
import time
from datetime import datetime, timedelta, timezone
from typing import Optional
import io
try:
    from PIL import Image, ImageDraw, ImageFont
    _PIL_AVAILABLE = True
except ImportError:
    _PIL_AVAILABLE = False

try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

TOKEN                = os.getenv("TOKEN", "")
DATABASE_URL         = os.getenv("DATABASE_URL", "")
LOG_CHANNEL_ID       = 0   # game-log
FINANCE_LOG_ID       = 0   # finance-log
INVITE_LOG_ID        = 0   # invite-log
REWARD_LOG_ID        = 0   # rewards-log (rain, promo, daily, boost — set via /setrewardlog)
TIP_LOG_ID             = 0   # tip-log (admin only)
TIP_PUBLIC_LOG_ID      = 0   # tipping  (public in Extra)
VOUCHES_CHANNEL_ID   = 0   # vouches (public activity feed)
CASE_BATTLE_LOG_ID   = 0   # case-battles channel
CASE_BATTLE_CHANNEL_ID = 0  # case-battles channel (same, set by auto-setup)

async def _load_channel_ids():
    """Load channel IDs saved by /setup from the DB into globals."""
    global LOG_CHANNEL_ID, FINANCE_LOG_ID, INVITE_LOG_ID, REWARD_LOG_ID, TIP_LOG_ID, TIP_PUBLIC_LOG_ID
    global CASE_BATTLE_LOG_ID, VOUCHES_CHANNEL_ID, CASE_BATTLE_CHANNEL_ID
    try:
        conn = await get_conn()
        try:
            rows = await conn.fetch("SELECT key, value FROM bot_settings WHERE key LIKE 'channel_%'")
            for r in rows:
                val = int(r["value"]) if r["value"].isdigit() else 0
                if r["key"] == "channel_game_log":        LOG_CHANNEL_ID     = val
                elif r["key"] == "channel_vouches":        VOUCHES_CHANNEL_ID = val
                elif r["key"] == "channel_finance_log":   FINANCE_LOG_ID     = val
                elif r["key"] == "channel_invite_log":    INVITE_LOG_ID      = val
                elif r["key"] == "channel_reward_log":    REWARD_LOG_ID      = val
                elif r["key"] == "channel_tip_log":       TIP_LOG_ID         = val
                elif r["key"] == "channel_tip_public":    TIP_PUBLIC_LOG_ID  = val
                elif r["key"] == "channel_case_battles":
                    CASE_BATTLE_LOG_ID     = val
                    CASE_BATTLE_CHANNEL_ID = val
        finally:
            await release_conn(conn)
        print(f"[BOT] Channel IDs loaded from DB")
    except Exception as e:
        print(f"[BOT] Could not load channel IDs: {e}")
ADMIN_ROLE_NAME      = "Admin"
STAFF_ROLE_NAME      = "Moderator"
OWNER_ROLE_NAME      = "Owner"
MANAGER_ROLE_NAME    = "Manager"
TMOD_ROLE_NAME       = "t-Mod"
BOT_HOUSE_WIN        = 0.52   # 52/48 edge across all games
BJ_DEALER_STAND      = 17    # Dealer stands at this total (16=player friendly, 17=standard, 19=heavy edge)

GUILD_ID             = int(os.getenv("GUILD_ID", "1481262963569594423"))  # Set your server ID in env vars

_pool: asyncpg.Pool = None

RANK_DATA = [
    (0,                10_000_000,   "🥉", "Bronze",      0xCD7F32),   # 0 – 10M gems
    (10_000_000,       50_000_000,   "🥈", "Silver",      0xC0C0C0),   # 10M – 50M
    (50_000_000,       200_000_000,  "🥇", "Gold",        0xFFD700),   # 50M – 200M
    (200_000_000,      600_000_000,  "💿", "Platinum",    0xE5E4E2),   # 200M – 600M
    (600_000_000,      1_500_000_000,"🔴", "Ruby",        0x9B111E),   # 600M – 1.5B
    (1_500_000_000,    3_000_000_000,"💚", "Emerald",     0x50C878),   # 1.5B – 3B
    (3_000_000_000,    5_000_000_000,"🎰", "High Roller", 0xFF6600),   # 3B – 5B
    (5_000_000_000,   10_000_000_000,"🐋", "Whale",       0x1E90FF),   # 5B – 10B
    (10_000_000_000,  10**18,        "🏆", "Legend",      0xFFD700),   # 10B+
]

CHAMPION_ROLE     = "👑 Champion"      # Top 1 on leaderboard
DIAMOND_WHALE_ROLE = "💎 Diamond Whale" # Top 2–3 on leaderboard
MEMBER_ROLE_NAME     = "Member"          # Manually assigned after verification
UNVERIFIED_ROLE_NAME = "Unverified"      # Auto-assigned to everyone on join
BOT_ROLE_NAME        = "bloxysab"        # Top-level bot management role — sits above all casino roles
VERIFIED_ROLE_NAME   = "Verified"       # Auto-created verified role

CARD_EMOJIS = {
    1: "🎲", 2: "⚽", 3: "3️⃣", 4: "4️⃣", 5: "5️⃣",
    6: "6️⃣", 7: "🔥", 8: "8️⃣", 9: "9️⃣", 10: "🔟",
    11: "👑", 12: "👸", 13: "🤴",
}

DICE_EMOJIS = ["⚀", "⚁", "⚂", "⚃", "⚄", "⚅"]

ROULETTE_OUTCOMES = [
    ("🔴", "Red",    0.475, 2.0),   # 5% house edge on even-money bets
    ("🔵", "Blue",   0.475, 2.0),
    ("🟡", "Yellow", 0.05,  6.0),
]

_user_locks: dict[int, asyncio.Lock] = {}

def get_user_lock(user_id: int) -> asyncio.Lock:
    if user_id not in _user_locks:
        _user_locks[user_id] = asyncio.Lock()
    return _user_locks[user_id]

_active_games: set[int] = set()

def _start_game_session(user_id: int) -> bool:
    """Returns True if session started, False if user already in a game."""
    if user_id in _active_games:
        return False
    _active_games.add(user_id)
    return True

def _end_game_session(user_id: int) -> None:
    _active_games.discard(user_id)

_cooldowns: dict[str, dict[int, float]] = {}
GAME_COOLDOWN_SECONDS = 3

_force_result: dict[int, str] = {}

def get_dynamic_house_win(user_id: int, current_balance: int = 0) -> float:
    """Flat 53% house win rate. No pity system."""
    forced = _force_result.pop(user_id, None)
    if forced == "win":  return 0.0
    if forced == "lose": return 1.0
    return BOT_HOUSE_WIN

def record_streak(user_id: int, won: bool, current_balance: int = 0):
    pass  # No-op — pity system removed

def check_cooldown(command: str, user_id: int) -> float:
    """Returns 0 if allowed, seconds remaining if on cooldown."""
    now = time.monotonic()
    if command not in _cooldowns:
        _cooldowns[command] = {}
    last = _cooldowns[command].get(user_id, 0)
    remaining = GAME_COOLDOWN_SECONDS - (now - last)
    if remaining > 0:
        return remaining
    _cooldowns[command][user_id] = now
    return 0

MAX_BET    = 750_000_000   # 750M gems
MAX_PAYOUT = 1_650_000_000 # 1.65B gems
MIN_BET    = 100_000       # 100K gems

LOCKED_GAMES: set = set()

ALL_GAMES = {
    "🪙 Coinflip":           "coinflip",
    "🎲 Dice":               "dice",
    "🃏 Blackjack":          "blackjack",
    "🎲 Blackjack Dice":     "blackjackdice",
    "🎡 Roulette":           "roulette",
    "🎴 Baccarat":           "baccarat",
    "⚔️ War":                "war",
    "🔼 HiLo":               "hilo",
    "🗼 Towers":             "towers",
    "💣 Mines":              "mines",
    "🎰 Slots":              "slots",
    "🏇 Horse Race":         "horserace",
    "🎟️ Scratch":            "scratch",
    "🎨 Color Dice":         "colordice",
    "📈 Progressive Coinflip": "progressivecoinflip",
    "⚔️ Case Battle":        "createcasebattle",
}

ALLOWED_LOCK_ROLES = {
    "Owner", "Admin", "Moderator",
    "Member", "Verified", "💎 VIP",
}

def is_game_locked(game_key: str, member) -> bool:
    """Returns True if the game is locked AND the member has none of the allowed roles."""
    if game_key not in LOCKED_GAMES:
        return False
    member_role_names = {r.name for r in member.roles}
    bypass_roles = {"Owner", "Manager", "Admin", "Moderator", "t-Mod"}
    return not bool(member_role_names & bypass_roles)

DAILY_MIN = 1          # 1 gem
DAILY_MAX = 10_000_000 # 10M gems

_invite_cache: dict[int, dict[str, int]] = {}

SUFFIXES = [
    (1_000_000_000_000, "T"),
    (1_000_000_000,     "B"),
    (1_000_000,         "M"),
    (1_000,             "K"),
]
POINT_SCALE = 1

def parse_amount(text: str) -> Optional[int]:
    """Parse a gem amount from user input. Supports integers (5), K/M/B/T suffixes (1K, 2.5M).
    1 internal unit = 1 gem displayed."""
    if not text:
        return None
    text = text.strip().upper().replace(",", "")
    multipliers = {"K": 1_000, "M": 1_000_000, "B": 1_000_000_000, "T": 1_000_000_000_000}
    try:
        if text[-1] in multipliers:
            val = int(float(text[:-1]) * multipliers[text[-1]])
        else:
            val = int(float(text))
        return val if val > 0 else None
    except (ValueError, IndexError):
        return None

C_GOLD   = 0xA855F7   # neon purple   — brand (bloxysab logo)
C_WIN    = 0x7C3AED   # deep violet   — win
C_LOSS   = 0xFC3D5F   # crimson       — loss
C_PUSH   = 0x6D28D9   # indigo        — push/tie
C_BLUE   = 0x9333EA   # vivid purple  — info
C_VIP    = 0xE879F9   # neon magenta  — VIP
C_WARN   = 0xF59E0B   # amber         — warning
C_DARK   = 0x1A1025   # deep dark     — inactive

CASINO_MARK = "BLOXYSAB  ╱  bloxysab.gg"
LOGO_URL = os.getenv("LOGO_URL", "")  # Paste your bloxysab logo URL here or set LOGO_URL env var
COINFLIP_HEADS_GIF    = os.getenv("COINFLIP_HEADS_GIF",    "https://i.imgur.com/hgH4kFf.gif")
COINFLIP_TAILS_GIF    = os.getenv("COINFLIP_TAILS_GIF",    "https://i.imgur.com/tUmaoHl.gif")
COINFLIP_SPINNING_GIF = os.getenv("COINFLIP_SPINNING_GIF", "")  # Optional spinning GIF while flipping

DICE_GIF = [
    os.getenv("DICE_GIF_1", "https://cdn.discordapp.com/attachments/1497626985315307621/1497964042218639380/1filedice1-ezgif.com-effects.gif?ex=69ef6f3a&is=69ee1dba&hm=04c274ca0f29a0e2734eb9e69594e5be6b0ee843402c6b63ec89cd1199b1fbd6&"),  # 1
    os.getenv("DICE_GIF_2", "https://cdn.discordapp.com/attachments/1497626985315307621/1497963571307614218/2_dice_1.gif?ex=69ef6eca&is=69ee1d4a&hm=8d6eeb6bd4a9d7da7b523cc7d5964d9e6692f91a72d76176f5cbcea4dcb77acf&"),  # 2
    os.getenv("DICE_GIF_3", "https://cdn.discordapp.com/attachments/1497626985315307621/1497964050859167925/3_dice_gif_gif.gif?ex=69ef6f3c&is=69ee1dbc&hm=8642b4f8e4ebab95c6779d743ee240e3c7565f98f567c7705998e1521fed5de0&"),  # 3
    os.getenv("DICE_GIF_4", "https://cdn.discordapp.com/attachments/1497626985315307621/1497963860274184262/4_dicess.gif?ex=69ef6f0f&is=69ee1d8f&hm=5f0e3e3f064d081678226385518c11409cfda6a55d908ff800d0561b271af304&"),  # 4
    os.getenv("DICE_GIF_5", "https://cdn.discordapp.com/attachments/1497626985315307621/1497963744154747061/5_dices_orig.gif?ex=69ef6ef3&is=69ee1d73&hm=e215812c82248af16df99ed4cdac5f4c0b5c374e8c79c5a5a46da4510af5314d&"),  # 5
    os.getenv("DICE_GIF_6", "https://cdn.discordapp.com/attachments/1497626985315307621/1497963851713347746/6_dice_orig.gif?ex=69ef6f0d&is=69ee1d8d&hm=93e5015a861664e3339c4b3eb8184f1aaff2c37adfd84d9511e91f268da59a9e&"),  # 6
]

def get_dice_gif(roll: int) -> str:
    """Return the GIF URL for a given dice roll (1-6)."""
    if 1 <= roll <= 6:
        return DICE_GIF[roll - 1]
    return ""

def _brand_embed(embed: discord.Embed) -> discord.Embed:
    """Apply bloxysab branding: logo as small author icon + footer."""
    embed.set_author(name="✦ BLOXYSAB", icon_url=LOGO_URL if LOGO_URL else None)
    embed.set_footer(text=CASINO_MARK)
    return embed

DIV_THICK = "▬" * 14
DIV_THIN  = "┄" * 18
DIV_DOT   = "· " * 9

SUIT_COLOR = {"♠": "⬛", "♥": "🟥", "♦": "🟥", "♣": "⬛"}

def _bar(filled: int, total: int = 10, fill="█", empty="░") -> str:
    filled = max(0, min(total, filled))
    return fill * filled + empty * (total - filled)

def _money(n: int, sign: bool = False) -> str:
    """Bold formatted amount with optional +/- sign."""
    s = format_amount(n)
    if sign:
        return f"**+{s}**" if n >= 0 else f"**-{format_amount(abs(n))}**"
    return f"**{s}**"

def _row(*cols, width: int = 18) -> str:
    """Fixed-width monospace row for code blocks."""
    return "  ".join(str(c).ljust(width) for c in cols)

def game_header(name: str, bet: int, extra: str = "") -> str:
    """Consistent game description header."""
    lines = [f"```ansi\n\u001b[35m  {name.upper():<16}\u001b[0m  {format_amount(bet):>14}", "```"]
    if extra:
        lines.insert(1, f"  {extra[:32]}")
    return "\n".join(lines)

def result_desc(won: bool, is_push: bool, bet: int, payout: int) -> str:
    """Game result block — inline markdown style, no code block."""
    net = payout - bet
    if is_push:
        badge   = "🔁  **PUSH**"
        net_txt = "> `±0`  bet returned"
    elif won:
        badge   = "🟢  **WIN**"
        net_txt = f"> `+{format_amount(net)}` 💎  profit"
    else:
        badge   = "🔴  **LOSS**"
        net_txt = f"> `-{format_amount(bet)}` 💎  lost"
    return (
        f"{badge}\n"
        f"{net_txt}\n"
        f"> Bet **{format_amount(bet)}** 💎  ·  Returned **{format_amount(payout)}** 💎"
    )

_roblox_avatar_cache: dict[int, str | None] = {}

async def get_roblox_avatar_url(discord_user_id: int) -> str | None:
    """Return Roblox headshot URL for a linked user, or None if not linked. Memory-cached."""
    if discord_user_id in _roblox_avatar_cache:
        return _roblox_avatar_cache[discord_user_id]
    conn = await get_conn()
    try:
        row = await conn.fetchrow(
            "SELECT roblox_id FROM roblox_links WHERE user_id=$1",
            str(discord_user_id)
        )
    except Exception:
        row = None
    finally:
        await release_conn(conn)
    if not row:
        _roblox_avatar_cache[discord_user_id] = None
        return None
    roblox_id = row["roblox_id"]
    try:
        import aiohttp
        async with aiohttp.ClientSession() as session:
            async with session.get(
                f"https://thumbnails.roblox.com/v1/users/avatar-headshot"
                f"?userIds={roblox_id}&size=420x420&format=Png&isCircular=false"
            ) as resp:
                if resp.status == 200:
                    data = await resp.json()
                    url = data["data"][0]["imageUrl"]
                    _roblox_avatar_cache[discord_user_id] = url
                    return url
    except Exception as e:
        print(f"[ROBLOX] Avatar fetch failed for {roblox_id}: {e}")
    _roblox_avatar_cache[discord_user_id] = None
    return None

async def get_avatar(user: discord.User | discord.Member) -> str:
    """Return Roblox headshot if linked, otherwise Discord avatar."""
    roblox = await get_roblox_avatar_url(user.id)
    return roblox if roblox else user.display_avatar.url

def format_amount(n: int) -> str:
    """Format an internal value as display gems. 1 internal unit = 1 gem.
    1000 → '1K', 1500000 → '1.5M', 1000000000 → '1B'"""
    if n < 0:
        return f"-{format_amount(-n)}"
    display = n
    for threshold, suffix in SUFFIXES:
        if display >= threshold:
            val = display / threshold
            if val == int(val):
                return f"{int(val)}{suffix}"
            return f"{val:.2f}".rstrip("0").rstrip(".") + suffix
    return str(int(display))

def progress_bar(current: int, maximum: int, length: int = 12) -> str:
    if maximum == math.inf or maximum == 0:
        filled = length
    else:
        filled = int(min(current / maximum, 1.0) * length)
    return f"[{'█' * filled}{'░' * (length - filled)}]"

def get_rank(wagered: int) -> tuple:
    for low, high, emoji, name, color in RANK_DATA:
        if wagered < high:
            return emoji, name, low, high, color
    last = RANK_DATA[-1]
    return last[2], last[3], last[0], math.inf, last[4]

def is_admin(member) -> bool:
    """Works for both Member (guild) and User (DM) objects."""
    if hasattr(member, "roles"):
        return any(r.name in (ADMIN_ROLE_NAME, OWNER_ROLE_NAME) for r in member.roles)
    return False

async def is_admin_user(user: discord.User) -> bool:
    """Fetch guild member to check admin roles — used for DM command auth."""
    guild = bot.get_guild(GUILD_ID)
    if not guild:
        return False
    try:
        member = guild.get_member(user.id) or await guild.fetch_member(user.id)
        return is_admin(member)
    except Exception:
        return False

def now_ts() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
async def require_linked(interaction: discord.Interaction) -> bool:
    """Check if the user has linked their Roblox account. If not, send ephemeral error and return False."""
    if hasattr(interaction, '_command_name') and interaction._command_name == 'link':
        return True
    conn = await get_conn()
    try:
        row = await conn.fetchrow(
            "SELECT roblox_username FROM roblox_links WHERE user_id=$1",
            str(interaction.user.id)
        )
    except Exception:
        row = None
    finally:
        await release_conn(conn)
    if row:
        return True
    e = discord.Embed(
        color=C_LOSS,
        description=(
            "## 🔗  LINK REQUIRED\n"
            "You need to link your **Roblox account** before playing.\n"
            "─────────────────────────────\n"
            "> `/link <username>` — connect your account\n"
            "> Your avatar will appear on all game embeds"
        )
    )
    _brand_embed(e)
    try:
        if interaction.response.is_done():
            await interaction.followup.send(embed=e, ephemeral=True)
        else:
            await interaction.response.send_message(embed=e, ephemeral=True)
    except Exception:
        pass
    return False

async def db_connect():
    """Get a connection from the pool."""
    return await _pool.acquire()

async def db_release(conn):
    """Return connection to pool."""
    await _pool.release(conn)

async def init_db():
    global _pool
    if not DATABASE_URL:
        print("❌ DATABASE_URL not set!")
        return
    try:
        _pool = await asyncpg.create_pool(
            DATABASE_URL,
            min_size=2,
            max_size=10,
            command_timeout=30,
            ssl="require"
        )
    except Exception as e:

        print(f"[ERROR] {type(e).__name__}: {e}")
        _pool = await asyncpg.create_pool(
            DATABASE_URL,
            min_size=2,
            max_size=10,
            command_timeout=30
        )

    async with _pool.acquire() as conn:
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS users (
                user_id          TEXT PRIMARY KEY,
                username         TEXT NOT NULL DEFAULT '',
                balance          BIGINT NOT NULL DEFAULT 0,
                wagered          BIGINT NOT NULL DEFAULT 0,
                wins             INTEGER NOT NULL DEFAULT 0,
                losses           INTEGER NOT NULL DEFAULT 0,
                streak           INTEGER NOT NULL DEFAULT 0,
                max_streak       INTEGER NOT NULL DEFAULT 0,
                tips_sent        BIGINT NOT NULL DEFAULT 0,
                tips_recv        BIGINT NOT NULL DEFAULT 0,
                total_deposited  BIGINT NOT NULL DEFAULT 0,
                created_at       TEXT NOT NULL DEFAULT '',
                last_updated     TEXT NOT NULL DEFAULT ''
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS stock (
                item_name  TEXT PRIMARY KEY,
                quantity   INTEGER NOT NULL DEFAULT 0,
                unit_value BIGINT NOT NULL DEFAULT 0
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS transactions (
                id       SERIAL PRIMARY KEY,
                user_id  TEXT NOT NULL,
                action   TEXT NOT NULL,
                amount   BIGINT NOT NULL,
                note     TEXT,
                ts       TEXT NOT NULL
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS withdrawals_queue (
                id           SERIAL PRIMARY KEY,
                user_id      TEXT NOT NULL,
                username     TEXT NOT NULL DEFAULT '',
                item_name    TEXT NOT NULL,
                quantity     INTEGER NOT NULL DEFAULT 1,
                total_cost   BIGINT NOT NULL DEFAULT 0,
                channel_id   TEXT NOT NULL DEFAULT '',
                status       TEXT NOT NULL DEFAULT 'pending',
                claimed_by   TEXT,
                completed_at TEXT,
                created_at   TEXT NOT NULL DEFAULT ''
            )
        """)
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_users_wagered ON users(wagered DESC)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_users_balance ON users(balance DESC)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_tx_user ON transactions(user_id)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_users_deposited ON users(total_deposited DESC)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_tx_action ON transactions(action)")
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS daily_claims (
                user_id   TEXT PRIMARY KEY,
                last_claim TEXT NOT NULL DEFAULT ''
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS giveaways (
                id          SERIAL PRIMARY KEY,
                channel_id  TEXT NOT NULL,
                message_id  TEXT NOT NULL,
                host_id     TEXT NOT NULL,
                host_name   TEXT NOT NULL DEFAULT '',
                prize       BIGINT NOT NULL,
                end_time    DOUBLE PRECISION NOT NULL,
                dur_label   TEXT NOT NULL,
                end_str     TEXT NOT NULL,
                ended       BOOLEAN NOT NULL DEFAULT FALSE
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS giveaway_entrants (
                giveaway_id INTEGER NOT NULL REFERENCES giveaways(id) ON DELETE CASCADE,
                user_id     TEXT NOT NULL,
                PRIMARY KEY (giveaway_id, user_id)
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS promocodes (
                code        TEXT PRIMARY KEY,
                amount      BIGINT NOT NULL,
                max_uses    INTEGER NOT NULL,
                uses        INTEGER NOT NULL DEFAULT 0,
                created_by  TEXT NOT NULL,
                active      BOOLEAN NOT NULL DEFAULT TRUE
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS promocode_redeems (
                code    TEXT NOT NULL,
                user_id TEXT NOT NULL,
                PRIMARY KEY (code, user_id)
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS invite_rewards (
                invitee_id   TEXT PRIMARY KEY,
                inviter_id   TEXT NOT NULL,
                rewarded_at  TEXT NOT NULL,
                reward_amt   BIGINT NOT NULL DEFAULT 0,
                wagered_so_far BIGINT NOT NULL DEFAULT 0,
                req_met      BOOLEAN NOT NULL DEFAULT FALSE
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS suspended_invite_rewards (
                user_id      TEXT PRIMARY KEY,
                suspended_at TEXT NOT NULL DEFAULT '',
                suspended_by TEXT NOT NULL DEFAULT ''
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS pending_verifications (
                member_id    TEXT PRIMARY KEY,
                guild_id     TEXT NOT NULL,
                inviter_id   TEXT,
                joined_at    TEXT NOT NULL DEFAULT ''
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS wager_requirements (
                user_id       TEXT PRIMARY KEY,
                required_amt  BIGINT NOT NULL DEFAULT 0,
                wagered_so_far BIGINT NOT NULL DEFAULT 0,
                req_met       BOOLEAN NOT NULL DEFAULT FALSE
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS admin_balances (
                admin_id      TEXT PRIMARY KEY,
                insurance     BIGINT NOT NULL DEFAULT 0,
                used          BIGINT NOT NULL DEFAULT 0,
                last_updated  TEXT NOT NULL DEFAULT ''
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS bot_settings (
                key   TEXT PRIMARY KEY,
                value TEXT NOT NULL
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS quest_progress (
                user_id  TEXT NOT NULL,
                date_str TEXT NOT NULL,
                quest_id TEXT NOT NULL,
                progress BIGINT NOT NULL DEFAULT 0,
                claimed  BOOLEAN NOT NULL DEFAULT FALSE,
                PRIMARY KEY (user_id, date_str, quest_id)
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS roblox_links (
                user_id         TEXT PRIMARY KEY,
                roblox_username TEXT NOT NULL,
                roblox_id       BIGINT NOT NULL,
                linked_at       TEXT NOT NULL
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS affiliate_codes (
                user_id         TEXT PRIMARY KEY,
                code            TEXT UNIQUE NOT NULL,
                pending_balance BIGINT NOT NULL DEFAULT 0,
                total_earned    BIGINT NOT NULL DEFAULT 0,
                referral_count  INT NOT NULL DEFAULT 0,
                created_at      TEXT NOT NULL
            )
        """)
        await conn.execute("""
            ALTER TABLE affiliate_codes ADD COLUMN IF NOT EXISTS pending_balance BIGINT NOT NULL DEFAULT 0
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS affiliate_uses (
                referral_id   TEXT PRIMARY KEY,
                referrer_id   TEXT NOT NULL,
                code          TEXT NOT NULL,
                total_wagered BIGINT NOT NULL DEFAULT 0,
                total_earned  BIGINT NOT NULL DEFAULT 0,
                used_at       TEXT NOT NULL
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS message_counts (
                user_id         TEXT PRIMARY KEY,
                total_count     BIGINT NOT NULL DEFAULT 0,
                unclaimed_miles INT    NOT NULL DEFAULT 0,
                total_claimed   INT    NOT NULL DEFAULT 0
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS achievements (
                user_id     TEXT NOT NULL,
                achievement TEXT NOT NULL,
                unlocked_at TEXT NOT NULL DEFAULT '',
                PRIMARY KEY (user_id, achievement)
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS user_stats (
                user_id         TEXT PRIMARY KEY,
                cf_wins         INTEGER NOT NULL DEFAULT 0,
                dice_wins       INTEGER NOT NULL DEFAULT 0,
                bj_wins         INTEGER NOT NULL DEFAULT 0,
                rlt_wins        INTEGER NOT NULL DEFAULT 0,
                mines_clears    INTEGER NOT NULL DEFAULT 0,
                mines_cashouts  INTEGER NOT NULL DEFAULT 0,
                towers_clears   INTEGER NOT NULL DEFAULT 0,
                hilo_cashouts   INTEGER NOT NULL DEFAULT 0,
                rps_wins        INTEGER NOT NULL DEFAULT 0,
                war_wins        INTEGER NOT NULL DEFAULT 0,
                baccarat_wins   INTEGER NOT NULL DEFAULT 0,
                scratch_wins    INTEGER NOT NULL DEFAULT 0,
                horse_wins      INTEGER NOT NULL DEFAULT 0,
                balloon_pops    INTEGER NOT NULL DEFAULT 0,
                balloon_cashouts INTEGER NOT NULL DEFAULT 0,
                upgrader_wins   INTEGER NOT NULL DEFAULT 0,
                cdice_wins      INTEGER NOT NULL DEFAULT 0,
                cb_wins         INTEGER NOT NULL DEFAULT 0,
                rain_count      INTEGER NOT NULL DEFAULT 0,
                biggest_win     BIGINT NOT NULL DEFAULT 0,
                worst_streak    INTEGER NOT NULL DEFAULT 0
            )
        """)
    print("[DB] PostgreSQL ready ✓")

async def ensure_user(conn, user: discord.User):
    if not user or not user.id:
        return
    exists = await conn.fetchrow("SELECT user_id FROM users WHERE user_id=$1", str(user.id))
    now = now_ts()
    username = getattr(user, 'name', str(user.id))
    if not exists:
        await conn.execute(
            """INSERT INTO users
               (user_id, username, balance, wagered, wins, losses,
                streak, max_streak, tips_sent, tips_recv, created_at, last_updated)
               VALUES ($1, $2, 0, 0, 0, 0, 0, 0, 0, 0, $3, $4)
               ON CONFLICT (user_id) DO NOTHING""",
            str(user.id), username, now, now
        )
    else:
        await conn.execute(
            "UPDATE users SET username=$1, last_updated=$2 WHERE user_id=$3",
            username, now, str(user.id)
        )

async def get_user(conn, user_id: int):
    return await conn.fetchrow("SELECT * FROM users WHERE user_id=$1", str(user_id))

async def add_wager_req(conn, user_id: int, amount: int, source: str = "reward"):
    """Add a wager requirement equal to the reward amount. Stacks on top of existing unfulfilled requirements."""
    if amount <= 0:
        return
    await conn.execute(
        """INSERT INTO wager_requirements (user_id, required_amt, wagered_so_far, req_met)
           VALUES ($1, $2, 0, FALSE)
           ON CONFLICT (user_id) DO UPDATE SET
               required_amt   = CASE WHEN wager_requirements.req_met THEN $2
                                     ELSE wager_requirements.required_amt + $2 END,
               wagered_so_far = CASE WHEN wager_requirements.req_met THEN 0
                                     ELSE wager_requirements.wagered_so_far END,
               req_met        = FALSE""",
        str(user_id), amount
    )
    print(f"[WAGER REQ] +{amount} for user {user_id} via {source}")

async def update_balance(conn, user_id: int, delta: int):
    """Add delta to balance (use negative delta to subtract, but prefer deduct_balance_safe for that)."""
    await conn.execute(
        "UPDATE users SET balance = balance + $1, last_updated = $2 WHERE user_id = $3",
        delta, now_ts(), str(user_id)
    )

WIN_TAX = 0.10  # 10% win tax on profits — PvP games only — overridden at runtime by /settax

async def get_win_tax(conn) -> float:
    """Fetch current tax rate from DB (defaults to 15%)."""
    try:
        row = await conn.fetchrow("SELECT value FROM bot_settings WHERE key='win_tax'")
        if row:
            val = float(row["value"])
            return val
        await conn.execute(
            "INSERT INTO bot_settings (key, value) VALUES ('win_tax', $1) ON CONFLICT DO NOTHING",
            str(WIN_TAX)
        )
    except Exception as _err:
        print(f"[TAX] get_win_tax error: {_err}")
    return WIN_TAX

_TAX_GAMES = {"coinflip", "progressive_coinflip", "dice", "war"}

async def apply_win_payout(conn, user_id: int, payout: int, bet: int, game: str = "") -> int:
    """
    Credit a win payout. Tax (10%) only applied on PvP games.
    Returns the actual amount credited.
    """
    if game in _TAX_GAMES:
        tax_rate = await get_win_tax(conn)
        profit   = max(0, payout - bet)
        tax      = int(profit * tax_rate)
        after_tax = payout - tax
        if tax > 0:
            await log_transaction(conn, user_id, f"{game}_tax", -tax,
                                  f"{tax_rate*100:.0f}% win tax on {format_amount(profit)} profit")
    else:
        after_tax = payout  # no tax on house games
    await update_balance(conn, user_id, after_tax)
    return after_tax

async def deduct_balance_safe(conn, user_id: int, amount: int) -> bool:
    """
    Atomically deduct `amount` only if balance >= amount.
    PostgreSQL UPDATE ... WHERE balance >= amount is fully atomic — no race condition.
    Returns True if deducted, False if insufficient funds.
    """
    result = await conn.execute(
        """UPDATE users SET balance = balance - $1, last_updated = $2
           WHERE user_id = $3 AND balance >= $1""",
        amount, now_ts(), str(user_id)
    )
    return result == "UPDATE 1"

async def set_balance_exact(conn, user_id: int, amount: int):
    await conn.execute(
        "UPDATE users SET balance=$1, last_updated=$2 WHERE user_id=$3",
        amount, now_ts(), str(user_id)
    )

RAKEBACK_EXCLUDED_GAMES = {"mines", "hilo", "upgrader", "balloon", "towers", "scratch", "slots", "colordice", "horserace"}

WAGER_REQ_EXCLUDED_GAMES = {"mines", "balloon", "towers", "hilo", "upgrader", "scratch", "slots", "colordice", "horserace"}

async def record_game(conn, user_id: int, won: bool, bet: int, payout: int, game: str = ""):
    """Record wagered + win/loss stats. Does NOT touch balance."""
    row = await get_user(conn, user_id)
    if not row:
        return
    streak = row["streak"]
    new_streak = (streak + 1 if streak >= 0 else 1) if won else (streak - 1 if streak <= 0 else -1)
    new_max = max(row["max_streak"], new_streak if new_streak > 0 else 0)
    wagered_increment = 0 if game in WAGER_REQ_EXCLUDED_GAMES else bet
    await conn.execute(
        """UPDATE users SET wagered=wagered+$1, wins=wins+$2, losses=losses+$3,
           streak=$4, max_streak=$5, last_updated=$6 WHERE user_id=$7""",
        wagered_increment, 1 if won else 0, 0 if won else 1, new_streak, new_max, now_ts(), str(user_id)
    )
    if game not in WAGER_REQ_EXCLUDED_GAMES:
        inv_row = await conn.fetchrow(
            "SELECT reward_amt, wagered_so_far, req_met FROM invite_rewards WHERE invitee_id=$1",
            str(user_id)
        )
        if inv_row and not inv_row["req_met"]:
            new_wagered = inv_row["wagered_so_far"] + bet
            req_met = new_wagered >= inv_row["reward_amt"]
            await conn.execute(
                "UPDATE invite_rewards SET wagered_so_far=$1, req_met=$2 WHERE invitee_id=$3",
                new_wagered, req_met, str(user_id)
            )
        wr_row = await conn.fetchrow(
            "SELECT required_amt, wagered_so_far, req_met FROM wager_requirements WHERE user_id=$1",
            str(user_id)
        )
        if wr_row and not wr_row["req_met"]:
            new_wagered = wr_row["wagered_so_far"] + bet
            req_met = new_wagered >= wr_row["required_amt"]
            await conn.execute(
                "UPDATE wager_requirements SET wagered_so_far=$1, req_met=$2 WHERE user_id=$3",
                new_wagered, req_met, str(user_id)
            )
    if game not in RAKEBACK_EXCLUDED_GAMES:
        await conn.execute(
            """INSERT INTO bot_settings (key, value) VALUES ($1, $2)
               ON CONFLICT (key) DO UPDATE SET value = (CAST(bot_settings.value AS BIGINT) + CAST($2 AS BIGINT))::TEXT""",
            f"rakeback_wagered_{user_id}", str(bet)
        )  # note: $2 stored as text but cast in query

    try:
        _GAME_WIN_COL = {
            "coinflip": "cf_wins", "progressive_coinflip": "cf_wins",
            "dice": "dice_wins",   "progressive_dice": "dice_wins",
            "blackjack": "bj_wins",
            "roulette": "rlt_wins",
            "rps": "rps_wins",
            "war": "war_wins",
            "baccarat": "baccarat_wins",
            "horserace": "horse_wins",
            "colordice": "cdice_wins",
            "upgrader": "upgrader_wins",
        }
        col = _GAME_WIN_COL.get(game)
        if won and col:
            await conn.execute(
                f"""INSERT INTO user_stats (user_id, {col}) VALUES ($1, 1)
                    ON CONFLICT (user_id) DO UPDATE SET {col} = user_stats.{col} + 1""",
                str(user_id)
            )
        if not won and new_streak < 0:
            loss_streak = abs(new_streak)
            await conn.execute(
                """INSERT INTO user_stats (user_id, worst_streak) VALUES ($1, $2)
                   ON CONFLICT (user_id) DO UPDATE
                   SET worst_streak = GREATEST(user_stats.worst_streak, $2)""",
                str(user_id), loss_streak
            )
        if won and payout > 0:
            await conn.execute(
                """INSERT INTO user_stats (user_id, biggest_win) VALUES ($1, $2)
                   ON CONFLICT (user_id) DO UPDATE
                   SET biggest_win = GREATEST(user_stats.biggest_win, $2)""",
                str(user_id), payout
            )
    except Exception as _se:
        print(f"[STATS] user_stats update error: {_se}")

    try:
        await update_quest_progress(conn, user_id, "play",  game, 1,   bet)
        await update_quest_progress(conn, user_id, "wager", game, bet, bet)
        if won:
            await update_quest_progress(conn, user_id, "win",    game, 1, bet)
            await update_quest_progress(conn, user_id, "streak", game, 1, bet)
        else:
            await reset_streak_quest(conn, user_id)  # reset streak quest progress on any loss
    except Exception as _qe:
        print(f"[QUESTS] progress error: {_qe}")

    try:
        await pay_affiliate(conn, user_id, bet)
    except Exception as _ae:
        print(f"[AFFILIATE] commission error: {_ae}")

    try:
        fresh_row = await get_user(conn, user_id)
        if fresh_row:
            await check_and_grant_achievements(conn, user_id, fresh_row)
    except Exception as _ace:
        print(f"[ACHIEVEMENTS] post-game check error: {_ace}")

async def log_transaction(conn, user_id: int, action: str, amount: int, note: str = ""):
    await conn.execute(
        "INSERT INTO transactions (user_id, action, amount, note, ts) VALUES ($1,$2,$3,$4,$5)",
        str(user_id), action, amount, note, now_ts()
    )
    _ach_triggers = {"daily", "rain_recv", "promo_redeem", "tip_sent", "casebattle_entry", "casebattle_win"}
    if action in _ach_triggers:
        try:
            fresh_row = await get_user(conn, user_id)
            if fresh_row:
                await check_and_grant_achievements(conn, user_id, fresh_row)
        except Exception as _ace:
            print(f"[ACHIEVEMENTS] log_transaction check error: {_ace}")

async def ensure_rank_roles(guild: discord.Guild):
    """Ensure all wager-threshold rank roles exist.
    Champion and Diamond Whale are leaderboard-only and managed by the hourly loop."""
    if not guild:
        return
    for low, high, emoji, name, color in RANK_DATA:
        role_name = f"{emoji} {name}"
        existing = discord.utils.get(guild.roles, name=role_name)
        if not existing:
            try:
                await guild.create_role(
                    name=role_name,
                    color=discord.Color(color),
                    hoist=True,
                    mentionable=False,
                    permissions=NO_PING_PERMISSIONS,
                    reason="Auto-created rank role"
                )
                print(f"[ROLES] Created role: {role_name} in {guild.name}")
            except Exception as e:
                print(f"[ROLES] Failed to create {role_name} in {guild.name}: {e}")
        else:
            edits = {}
            if existing.color.value != color:
                edits["color"] = discord.Color(color)
            await _strip_ping_perms(existing)
            if edits:
                try:
                    await existing.edit(**edits)
                except Exception as e:
                    print(f"[ERROR] {type(e).__name__}: {e}")
    for role_name, color in [(CHAMPION_ROLE, 0xFFD700), (DIAMOND_WHALE_ROLE, 0xB9F2FF)]:
        existing = discord.utils.get(guild.roles, name=role_name)
        if not existing:
            try:
                await guild.create_role(
                    name=role_name, color=discord.Color(color),
                    hoist=True, mentionable=False,
                    permissions=NO_PING_PERMISSIONS,
                    reason="Auto-created leaderboard role"
                )
                print(f"[ROLES] Created leaderboard role: {role_name} in {guild.name}")
            except Exception as e:
                print(f"[ROLES] Failed to create {role_name}: {e}")
        else:
            await _strip_ping_perms(existing)

MEMBER_ROLE_PERMISSIONS = discord.Permissions(
    send_messages=True,
    read_messages=True,
    read_message_history=True,
    add_reactions=True,
    use_external_emojis=True,
    attach_files=True,
    embed_links=True,
    connect=True,
    speak=True,
    use_voice_activation=True,
    mention_everyone=False,
    manage_messages=False,
    manage_channels=False,
    kick_members=False,
    ban_members=False,
    administrator=False,
    send_tts_messages=False,
)

NO_PING_PERMISSIONS = discord.Permissions(
    send_messages=True,
    read_messages=True,
    read_message_history=True,
    add_reactions=True,
    use_external_emojis=True,
    attach_files=True,
    embed_links=True,
    connect=True,
    speak=True,
    use_voice_activation=True,
    mention_everyone=False,
    send_tts_messages=False,
    manage_messages=False,
    manage_channels=False,
    kick_members=False,
    ban_members=False,
    administrator=False,
)

async def _strip_ping_perms(role: discord.Role):
    """Remove mention_everyone and send_tts from any role that has them."""
    if role.permissions.mention_everyone or role.permissions.send_tts_messages:
        try:
            new_perms = discord.Permissions(role.permissions.value)
            new_perms.update(mention_everyone=False, send_tts_messages=False)
            await role.edit(permissions=new_perms, reason="Auto: stripping @everyone/@here ping perms")
        except Exception as e:
            print(f"[ROLES] Could not strip ping perms from {role.name}: {e}")

async def strip_all_ping_perms(guild: discord.Guild):
    """
    Strip mention_everyone and send_tts from every role in the guild
    except roles with administrator permission (they keep all perms).
    Also strips from @everyone.
    """
    if not guild:
        return
    admin_role_names = {ADMIN_ROLE_NAME, OWNER_ROLE_NAME, MANAGER_ROLE_NAME, TMOD_ROLE_NAME}
    for role in guild.roles:
        if role.permissions.administrator:
            continue
        if role.name == BOT_ROLE_NAME:
            continue
        if role.name in {OWNER_ROLE_NAME, MANAGER_ROLE_NAME, ADMIN_ROLE_NAME, STAFF_ROLE_NAME, TMOD_ROLE_NAME}:
            continue
        await _strip_ping_perms(role)

async def ensure_bot_role(guild: discord.Guild) -> discord.Role | None:
    """
    Ensure the top-level Bot Management role exists and sits above all casino roles.
    The server owner should assign this role to the bot manually if the bot can't
    move itself (Discord requires a human to drag roles in hierarchy above bot's current top).
    We create it and position it as high as we can.
    """
    if not guild:
        return None
    existing = discord.utils.get(guild.roles, name=BOT_ROLE_NAME)
    if existing:
        return existing
    try:
        role = await guild.create_role(
            name=BOT_ROLE_NAME,
            color=discord.Color(C_GOLD),
            hoist=True,
            mentionable=False,
            permissions=discord.Permissions(administrator=False, manage_roles=True,
                                            manage_channels=True, kick_members=True,
                                            ban_members=True, send_messages=True,
                                            read_messages=True, embed_links=True),
            reason="Auto-created Bot Management role — move this above all casino roles"
        )
        try:
            bot_member = guild.me
            if bot_member and bot_member.top_role:
                max_pos = bot_member.top_role.position - 1
                if max_pos > role.position:
                    await role.edit(position=max_pos)
        except Exception:
            pass  # Position edit may fail if bot doesn't have high enough role yet
        print(f"[ROLES] Created bot management role: {BOT_ROLE_NAME} in {guild.name}")
        try:
            owner = guild.owner
            if owner:
                embed = discord.Embed(
                    title="✦  BLOXYSAB — Action Required",
                    description=(
                        f"bloxysab has created the **{BOT_ROLE_NAME}** role.\n\n"
                        f"**Action needed:** Move **{BOT_ROLE_NAME}** to the "
                        f"**top of your role list** in Server Settings → Roles so the bot can "
                        f"manage all roles properly.\n\n"
                        f"This only needs to be done once. ✦"
                    ),
                    color=C_GOLD
                )
                _brand_embed(embed)
                await owner.send(embed=embed)
        except Exception:
            pass
        return role
    except Exception as e:
        print(f"[ROLES] Failed to create bot role in {guild.name}: {e}")
        return None

async def ensure_member_role(guild: discord.Guild) -> discord.Role | None:
    """Ensure the Member role exists with correct permissions (no @everyone pings)."""
    if not guild:
        return None
    existing = discord.utils.get(guild.roles, name=MEMBER_ROLE_NAME)
    if existing:
        await _strip_ping_perms(existing)
        return existing
    try:
        role = await guild.create_role(
            name=MEMBER_ROLE_NAME,
            color=discord.Color(0x99AAB5),
            hoist=False,
            mentionable=False,
            permissions=MEMBER_ROLE_PERMISSIONS,
            reason="Auto-created Member role (no @everyone ping perms)"
        )
        print(f"[ROLES] Created Member role in {guild.name}")
        return role
    except Exception as e:
        print(f"[ROLES] Failed to create Member role in {guild.name}: {e}")
        return None

async def assign_member_role(member: discord.Member):
    """Give the Member role to a user if they don't have it."""
    if not member or not member.guild:
        return
    role = await ensure_member_role(member.guild)
    if role and role not in member.roles:
        try:
            await member.add_roles(role, reason="Auto-assigned Member role")
        except Exception as e:
            print(f"[ROLES] Could not assign Member role to {member}: {e}")

async def ensure_unverified_role(guild: discord.Guild) -> discord.Role | None:
    """Ensure the Unverified role exists; create it if missing."""
    existing = discord.utils.get(guild.roles, name=UNVERIFIED_ROLE_NAME)
    if existing:
        return existing
    try:
        role = await guild.create_role(
            name=UNVERIFIED_ROLE_NAME,
            color=discord.Color.from_rgb(100, 100, 100),
            hoist=False,
            reason="Auto-created Unverified role"
        )
        print(f"[ROLES] Created Unverified role in {guild.name}")
        return role
    except Exception as e:
        print(f"[ROLES] Failed to create Unverified role in {guild.name}: {e}")
        return None

async def ensure_staff_role(guild: discord.Guild) -> discord.Role | None:
    """
    Ensure the Moderator role exists in the guild.
    Creates it if missing, returns the role object.
    """
    if not guild:
        return None
    existing = discord.utils.get(guild.roles, name=STAFF_ROLE_NAME)
    if existing:
        return existing
    try:
        role = await guild.create_role(
            name=STAFF_ROLE_NAME,
            color=discord.Color(C_BLUE),   # Deep sky blue — distinct from Admin gold
            hoist=True,
            mentionable=True,
            reason="Auto-created Moderator role"
        )
        print(f"[ROLES] Created staff role in {guild.name}")
        return role
    except Exception as e:
        print(f"[ROLES] Failed to create staff role in {guild.name}: {e}")
        return None

async def update_user_rank(member: discord.Member, wagered: int):
    """Update wagered-threshold rank roles. Does NOT touch Exclusive/Diamond Whale (managed hourly).
    Snail is assigned as soon as the user wagers any amount (wagered >= 1)."""
    if not member or not member.guild:
        return
    if wagered < 1:
        return
    emoji, name, low, high, color = get_rank(wagered)
    target_role_name = f"{emoji} {name}"
    target_role = discord.utils.get(member.guild.roles, name=target_role_name)
    if not target_role:
        await ensure_rank_roles(member.guild)
        target_role = discord.utils.get(member.guild.roles, name=target_role_name)
        if not target_role:
            return
    rank_roles = []
    for r_low, r_high, r_emoji, r_name, r_color in RANK_DATA:
        role = discord.utils.get(member.guild.roles, name=f"{r_emoji} {r_name}")
        if role:
            rank_roles.append(role)
    roles_to_remove = [r for r in rank_roles if r != target_role and r in member.roles]
    if roles_to_remove:
        try:
            await member.remove_roles(*roles_to_remove, reason="Rank update")
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass
    if target_role not in member.roles:
        try:
            await member.add_roles(target_role, reason=f"Rank updated to {name}")
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass

async def update_dynamic_ranks():
    """
    Hourly task — assigns Exclusive (top 10) and Diamond Whale (top 1)
    based on wagered leaderboard. Removes roles from players who dropped out.
    """
    conn = await get_conn()
    try:
        rows = await conn.fetch(
            "SELECT user_id, wagered FROM users ORDER BY wagered DESC LIMIT 3"
        )
    finally:
        await release_conn(conn)

    top3_ids   = [int(r["user_id"]) for r in rows]
    top1_id    = top3_ids[0] if len(top3_ids) >= 1 else None
    top2_3_ids = set(top3_ids[1:3])

    for guild in bot.guilds:
        champion_role = discord.utils.get(guild.roles, name=CHAMPION_ROLE)
        if not champion_role:
            try:
                champion_role = await guild.create_role(
                    name=CHAMPION_ROLE, color=discord.Color(0xFFD700),
                    hoist=True, permissions=NO_PING_PERMISSIONS,
                    reason="Auto-created leaderboard role")
            except Exception as e:
                print(f"[ERROR] {type(e).__name__}: {e}")
                champion_role = None

        diamond_whale_role = discord.utils.get(guild.roles, name=DIAMOND_WHALE_ROLE)
        if not diamond_whale_role:
            try:
                diamond_whale_role = await guild.create_role(
                    name=DIAMOND_WHALE_ROLE, color=discord.Color(0xB9F2FF),
                    hoist=True, permissions=NO_PING_PERMISSIONS,
                    reason="Auto-created leaderboard role")
            except Exception as e:
                print(f"[ERROR] {type(e).__name__}: {e}")
                diamond_whale_role = None

        for member in guild.members:
            uid = member.id
            is_top1   = uid == top1_id
            is_top2_3 = uid in top2_3_ids

            if champion_role:
                if is_top1 and champion_role not in member.roles:
                    try:
                        await member.add_roles(champion_role, reason="Top 1 leaderboard")
                    except Exception as e:
                        print(f"[ERROR] {type(e).__name__}: {e}")
                elif not is_top1 and champion_role in member.roles:
                    try:
                        await member.remove_roles(champion_role, reason="No longer top 1")
                    except Exception as e:
                        print(f"[ERROR] {type(e).__name__}: {e}")

            if diamond_whale_role:
                if is_top2_3 and diamond_whale_role not in member.roles:
                    try:
                        await member.add_roles(diamond_whale_role, reason="Top 2-3 leaderboard")
                    except Exception as e:
                        print(f"[ERROR] {type(e).__name__}: {e}")
                elif not is_top2_3 and diamond_whale_role in member.roles:
                    try:
                        await member.remove_roles(diamond_whale_role, reason="No longer top 2-3")
                    except Exception:
                        pass

    print(f"[RANKS] Leaderboard role update complete. Champion: {top1_id}, Diamond Whale: {top2_3_ids}")

intents = discord.Intents.default()
intents.members = True
intents.message_content = True

bot = commands.Bot(command_prefix="!", intents=intents)

async def channel_cleanup_loop():
    """Stub — placeholder for future channel cleanup logic."""
    await bot.wait_until_ready()
    while not bot.is_closed():
        await asyncio.sleep(3600)

async def hourly_rank_loop():
    """Background task — updates Exclusive and Diamond Whale roles every hour."""
    await bot.wait_until_ready()
    while not bot.is_closed():
        try:
            await update_dynamic_ranks()
        except Exception as e:
            print(f"[RANKS] Hourly rank update error: {e}")
        await asyncio.sleep(3600)  # 1 hour

async def _bootstrap_member_roles():
    """One-time startup task — ensure required roles exist and strip @everyone/@here
    ping perms from all non-admin roles. Member role is NOT auto-assigned; it is
    granted manually after verification. New joiners receive Unverified automatically."""
    await bot.wait_until_ready()
    for guild in bot.guilds:
        try:
            await strip_all_ping_perms(guild)
            await ensure_member_role(guild)
            await ensure_unverified_role(guild)
            print(f"[ROLES] Bootstrap complete for {guild.name} — Member/Unverified roles ensured, Member NOT auto-assigned")
        except Exception as e:
            print(f"[ROLES] Bootstrap error in {guild.name}: {e}")

@bot.event
async def on_ready():
    import traceback
    print(f"[BOT] Online as {bot.user} ({bot.user.id})")

    print(f"[BOT] Bot is in {len(bot.guilds)} guild(s): {[g.name for g in bot.guilds]}")
    async def _do_sync():
        await asyncio.sleep(2)
        try:
            import json, hashlib

            payload = sorted(
                [cmd.to_dict() for cmd in bot.tree.get_commands()],
                key=lambda c: c.get("name","")
            )
            current_hash = hashlib.md5(json.dumps(payload, sort_keys=True).encode()).hexdigest()

            conn = await get_conn()
            try:
                row = await conn.fetchrow("SELECT value FROM bot_settings WHERE key='cmd_hash'")
                last_hash = row["value"] if row else None
            finally:
                await release_conn(conn)

            if current_hash == last_hash:
                print(f"[BOT] ⏭️  Commands unchanged (hash match) — skipping sync")
                return

            if GUILD_ID:
                guild_obj = discord.Object(id=int(GUILD_ID))
                bot.tree.copy_global_to(guild=guild_obj)
                synced = await bot.tree.sync(guild=guild_obj)
                print(f"[BOT] ✅ Guild sync OK: {len(synced)} commands registered to guild {GUILD_ID}")
            else:
                synced = await bot.tree.sync()
                print(f"[BOT] ✅ Global sync OK: {len(synced)} commands registered")

            conn = await get_conn()
            try:
                await conn.execute(
                    "INSERT INTO bot_settings (key, value) VALUES ('cmd_hash', $1) "
                    "ON CONFLICT (key) DO UPDATE SET value=$1",
                    current_hash
                )
            finally:
                await release_conn(conn)

        except discord.HTTPException as e:
            print(f"[BOT] ❌ Sync HTTP error: {e.status} {e.text}")
        except Exception as e:
            print(f"[BOT] ❌ Sync error: {type(e).__name__}: {e}")
    asyncio.create_task(_do_sync())

    try:
        await init_db()
    except Exception as e:
        print(f"[BOT] DB init error: {e}")
    for guild in bot.guilds:
        try:
            await ensure_bot_role(guild)
            await ensure_rank_roles(guild)
            await ensure_staff_role(guild)
        except Exception as e:
            print(f"[BOT] Role setup error for {guild.name}: {e}")
        try:
            invites = await guild.invites()
            _invite_cache[guild.id] = {inv.code: inv.uses for inv in invites}
        except Exception as e:
            print(f"[INVITE] Could not cache invites for {guild.name}: {e}")
    print(f"[INVITE] Cached invites for {len(bot.guilds)} guild(s)")
    await restore_giveaways()
    await _restore_ticket_views()          # re-register pending ticket buttons
    bot.add_view(VerifyView())             # persistent verify button survives restarts

    try:
        conn = await get_conn()
        try:
            row = await conn.fetchrow("SELECT value FROM bot_settings WHERE key='cb_nerf_level'")
            if row:
                global CB_PLAYER_LUCK, CB_BOT_LUCK
                import json as _json
                try:
                    _cb = _json.loads(row["value"])
                    CB_PLAYER_LUCK = int(_cb.get("player", 35))
                    CB_BOT_LUCK    = int(_cb.get("bot", 65))
                    print(f"[BOT] CB luck loaded: player={CB_PLAYER_LUCK} bot={CB_BOT_LUCK}")
                except Exception:
                    pass  # value not yet in JSON format
        finally:
            await release_conn(conn)
    except Exception as e:
        print(f"[BOT] Could not load CB nerf level: {e}")
    await _load_channel_ids()
    asyncio.create_task(hourly_rank_loop())
    asyncio.create_task(_migrate_existing_balances())
    asyncio.create_task(_migrate_add_deposited_column())
    asyncio.create_task(_bootstrap_member_roles())
    asyncio.create_task(_snapshot_all_members())
    asyncio.create_task(_daily_dm_loop())
    asyncio.create_task(_auto_create_roles())
    asyncio.create_task(_auto_create_channels())
    asyncio.create_task(channel_cleanup_loop())

async def _auto_create_roles():
    """Auto-create only the required staff/member roles on startup if they don't exist yet.
    Roles created: t-Mod, Moderator, Admin, Manager, Owner, Unverified, Member.
    Unverified is auto-assigned on join; Member is manually assigned after verification."""
    await asyncio.sleep(3)
    guild = bot.get_guild(GUILD_ID)
    if not guild:
        return
    roles_to_create = [
        (OWNER_ROLE_NAME,       discord.Color.from_rgb(255, 215, 0),    True),   # Owner
        (MANAGER_ROLE_NAME,     discord.Color.from_rgb(255, 140, 0),    True),   # Manager
        (ADMIN_ROLE_NAME,       discord.Color.from_rgb(255, 100, 0),    True),   # Admin
        (STAFF_ROLE_NAME,       discord.Color.from_rgb(100, 180, 255),  True),   # Moderator
        (TMOD_ROLE_NAME,        discord.Color.from_rgb(120, 200, 120),  True),   # t-Mod
        (MEMBER_ROLE_NAME,      discord.Color.from_rgb(150, 150, 150),  False),  # Member (manually assigned)
        (UNVERIFIED_ROLE_NAME,  discord.Color.from_rgb(100, 100, 100),  False),  # Unverified (auto on join)
    ]
    created = []
    for name, color, hoist in roles_to_create:
        if not discord.utils.get(guild.roles, name=name):
            try:
                await guild.create_role(name=name, color=color, hoist=hoist, reason="Auto-created on startup")
                created.append(name)
            except Exception as e:
                print(f"[ROLES] Could not create '{name}': {e}")
    if created:
        print(f"[ROLES] Auto-created {len(created)} roles: {chr(44).join(created)}")
    else:
        print("[ROLES] All required roles already exist")

    await _enforce_bot_role_position(guild)

async def _enforce_bot_role_position(guild: discord.Guild):
    """Ensure the bot's top role is positioned above all management/staff roles."""
    if not guild:
        return
    bot_member = guild.me
    if not bot_member:
        return
    management_role_names = {BOT_ROLE_NAME, OWNER_ROLE_NAME, MANAGER_ROLE_NAME, ADMIN_ROLE_NAME, STAFF_ROLE_NAME, TMOD_ROLE_NAME}
    management_roles = [r for r in guild.roles if r.name in management_role_names and r != bot_member.top_role]
    if not management_roles:
        return
    highest_mgmt = max(management_roles, key=lambda r: r.position)
    if bot_member.top_role.position <= highest_mgmt.position:
        try:
            target_pos = highest_mgmt.position + 1
            max_pos = bot_member.top_role.position
            if target_pos > max_pos:
                target_pos = max_pos
            bot_role = discord.utils.get(guild.roles, name=BOT_ROLE_NAME)
            if bot_role and bot_role.position < target_pos:
                await bot_role.edit(position=target_pos, reason="Auto: keeping bot role above management roles")
                print(f"[ROLES] Repositioned {BOT_ROLE_NAME} to position {target_pos}")
        except Exception as e:
            print(f"[ROLES] Could not reposition bot role: {e}")

async def _auto_create_channels():
    """Auto-create the full server channel layout on startup if channels don't exist.
    Permissions:
      - Most channels: Owner + Manager can read/write. Everyone else read-only or locked.
      - Gambling rooms: Members can type. Unverified cannot see.
      - Staff channels: Staff roles only.
      - @everyone: locked out of everything by default unless explicitly granted.
    """
    await asyncio.sleep(5)
    await _load_channel_ids()

    for guild in bot.guilds:
        try:
            await _setup_guild_channels(guild)
        except Exception as e:
            print(f"[SETUP] Channel setup error in {guild.name}: {e}")

async def _setup_guild_channels(guild: discord.Guild):
    """Create all channels and categories for a guild if they don't already exist."""

    def role(name): return discord.utils.get(guild.roles, name=name)

    everyone       = guild.default_role
    owner_role     = role(OWNER_ROLE_NAME)
    manager_role   = role(MANAGER_ROLE_NAME)
    admin_role     = role(ADMIN_ROLE_NAME)
    mod_role       = role(STAFF_ROLE_NAME)
    tmod_role      = role(TMOD_ROLE_NAME)
    member_role    = role(MEMBER_ROLE_NAME)
    unverified_role = role(UNVERIFIED_ROLE_NAME)
    bot_member     = guild.me

    LOCK    = discord.PermissionOverwrite(read_messages=False, send_messages=False)
    VISIBLE = discord.PermissionOverwrite(read_messages=True,  send_messages=False)  # read only
    FULL    = discord.PermissionOverwrite(read_messages=True,  send_messages=True)
    BOT_OW  = discord.PermissionOverwrite(read_messages=True,  send_messages=True, manage_messages=True)

    def staff_full(*roles):
        """Overwrites dict: everyone locked, listed roles get full access, bot gets full."""
        ow = {everyone: LOCK, bot_member: BOT_OW}
        for r in roles:
            if r: ow[r] = FULL
        return ow

    def announce_ow():
        """Owner/Manager can post. Everyone else read-only (members can react)."""
        ow = {everyone: LOCK, bot_member: BOT_OW}
        if owner_role:   ow[owner_role]   = FULL
        if manager_role: ow[manager_role] = FULL
        if admin_role:   ow[admin_role]   = VISIBLE
        if mod_role:     ow[mod_role]     = VISIBLE
        if tmod_role:    ow[tmod_role]    = VISIBLE
        if member_role:  ow[member_role]  = VISIBLE
        return ow

    def read_only_ow():
        """Owner/Manager write. All staff + members read. Unverified locked."""
        ow = announce_ow()
        return ow

    def chat_ow():
        """Members can chat. Unverified locked out."""
        ow = {everyone: LOCK, bot_member: BOT_OW}
        if owner_role:    ow[owner_role]    = FULL
        if manager_role:  ow[manager_role]  = FULL
        if admin_role:    ow[admin_role]    = FULL
        if mod_role:      ow[mod_role]      = FULL
        if tmod_role:     ow[tmod_role]     = FULL
        if member_role:   ow[member_role]   = FULL
        return ow

    def gambling_ow():
        """Members can gamble. Unverified locked. Staff can see."""
        return chat_ow()

    def staff_only_ow(*roles):
        """Only listed staff roles + Owner/Manager. Everyone else locked."""
        ow = {everyone: LOCK, bot_member: BOT_OW}
        if owner_role:   ow[owner_role]   = FULL
        if manager_role: ow[manager_role] = FULL
        for r in roles:
            if r: ow[r] = FULL
        return ow

    def vip_category_ow():
        """VIP category — locked to everyone, rooms created inside by bot."""
        ow = {everyone: LOCK, bot_member: BOT_OW}
        if owner_role:   ow[owner_role]   = FULL
        if manager_role: ow[manager_role] = FULL
        return ow

    layout = [
        ("📋 RULES", staff_full(owner_role, manager_role), [
            ("📖｜rules", "Read the rules before participating.", read_only_ow(), False),
        ]),
        ("❗ IMPORTANT", staff_full(owner_role, manager_role), [
            ("📣｜announcements",     "Server announcements.",           announce_ow(), False),
            ("🤖｜bot-announcements", "Bot updates and notifications.",  announce_ow(), False),
            ("🎊｜giveaways",         "Giveaway announcements.",         announce_ow(), False),
            ("✅｜are-we-legit",      "Proof of legitimacy.",            read_only_ow(), False),
        ]),
        ("💼 Extra", staff_full(owner_role, manager_role), [
            ("🎁｜tips",           "Tips and tricks.",          chat_ow(),      False),
            ("⭐｜rain",            "Rain rewards.",             chat_ow(),      False),
            ("🏷️｜promo-codes",    "Promo codes.",              read_only_ow(), False),
            ("💜｜boost-rewards",  "Server boost rewards.",     read_only_ow(), False),
            ("📤｜withdrawals",  "Submit your withdrawal requests here.", chat_ow(),      False),
        ]),
        ("💬 Chat", staff_full(owner_role, manager_role), [
            ("🗨️｜general", "General chat.",    chat_ow(),  False),
            ("🖼️｜media",   "Share media.",     chat_ow(),  False),
            ("🤝｜vouch",   "Vouch for staff.", chat_ow(),  False),
        ]),
        ("👑 VIP GAMBLING", vip_category_ow(), [
        ]),
        ("🎰 Gambling", staff_full(owner_role, manager_role), [
            ("🎲｜room-1",           "Gambling room 1.",          gambling_ow(), False),
            ("🎲｜room-2",           "Gambling room 2.",          gambling_ow(), False),
            ("🤡｜hall-of-flip",    "Hall of flip.",            staff_only_ow(admin_role, mod_role, tmod_role),     False),
        ]),
        ("⚔️ SABPvp", staff_full(owner_role, manager_role), [
            ("🔷｜coinflip",    "PvP coinflip duels.",    staff_only_ow(admin_role, mod_role, tmod_role), False),
            ("🤖｜create-game", "Create a PvP game.",     gambling_ow(), False),
        ]),
        ("🔊 Voice Channels", staff_full(owner_role, manager_role), [
            ("General", None, chat_ow(), True),
        ]),
        ("🔒 Staff", staff_only_ow(admin_role, mod_role, tmod_role), [
            ("🛡️｜staff-chat",  "Staff only chat.",    staff_only_ow(admin_role, mod_role, tmod_role), False),
            ("📋｜mod-logs",    "Moderation logs.",    staff_only_ow(admin_role, mod_role),             False),
        ]),
    ]

    existing_categories = {c.name: c for c in guild.categories}
    existing_text       = {c.name: c for c in guild.text_channels}
    existing_voice      = {c.name: c for c in guild.voice_channels}

    for cat_name, cat_ow, channels in layout:
        if cat_name not in existing_categories:
            try:
                cat = await guild.create_category(cat_name, overwrites=cat_ow)
                print(f"[SETUP] Created category: {cat_name}")
            except Exception as e:
                print(f"[SETUP] Failed to create category '{cat_name}': {e}")
                continue
        else:
            cat = existing_categories[cat_name]

        for ch_name, topic, ch_ow, is_voice in channels:
            existing_pool = existing_voice if is_voice else existing_text
            if ch_name not in existing_pool:
                try:
                    if is_voice:
                        await guild.create_voice_channel(ch_name, category=cat, overwrites=ch_ow)
                    else:
                        await guild.create_text_channel(
                            ch_name, category=cat, topic=topic or "", overwrites=ch_ow
                        )
                    print(f"[SETUP] Created {'voice' if is_voice else 'text'} channel: {ch_name}")
                except Exception as e:
                    print(f"[SETUP] Failed to create channel '{ch_name}': {e}")

    await _load_channel_ids()
    print(f"[SETUP] Channel setup complete for {guild.name}")

async def _migrate_add_deposited_column():
    """One-time migration: add missing columns and tables to existing DBs."""
    conn = await get_conn()
    try:
        await conn.execute(
            "ALTER TABLE users ADD COLUMN IF NOT EXISTS total_deposited BIGINT NOT NULL DEFAULT 0"
        )
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS admin_balances (
                admin_id      TEXT PRIMARY KEY,
                insurance     BIGINT NOT NULL DEFAULT 0,
                used          BIGINT NOT NULL DEFAULT 0,
                last_updated  TEXT NOT NULL DEFAULT ''
            )
        """)
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS withdrawals_queue (
                id           SERIAL PRIMARY KEY,
                user_id      TEXT NOT NULL,
                username     TEXT NOT NULL DEFAULT '',
                item_name    TEXT NOT NULL,
                quantity     INTEGER NOT NULL DEFAULT 1,
                total_cost   BIGINT NOT NULL DEFAULT 0,
                channel_id   TEXT NOT NULL DEFAULT '',
                status       TEXT NOT NULL DEFAULT 'pending',
                claimed_by   TEXT,
                completed_at TEXT,
                created_at   TEXT NOT NULL DEFAULT ''
            )
        """)
        print("[MIGRATE] ✅ All migrations applied")
    except Exception as e:
        print(f"[MIGRATE] Error: {e}")
    finally:
        await release_conn(conn)

async def _migrate_existing_balances():
    """One-time migration: flag all existing users with balance > 0 who have no wager requirement.
    Uses a DB flag so it only ever runs once, not on every restart."""
    try:
        conn = await get_conn()
        try:
            flag = await conn.fetchrow(
                "SELECT value FROM bot_settings WHERE key='migration_wager_req_done'"
            )
            if flag:
                print("[MIGRATION] Wager requirement migration already ran — skipping.")
                return

            rows = await conn.fetch(
                """SELECT user_id, balance FROM users
                   WHERE balance > 0
                   AND user_id NOT IN (SELECT user_id FROM wager_requirements)
                   AND user_id NOT IN (SELECT invitee_id FROM invite_rewards WHERE req_met = FALSE)"""
            )
            if not rows:
                print("[MIGRATION] No existing users to flag for wager requirement.")
            else:
                for row in rows:
                    await conn.execute(
                        """INSERT INTO wager_requirements (user_id, required_amt, wagered_so_far, req_met)
                           VALUES ($1, $2, 0, FALSE)
                           ON CONFLICT (user_id) DO NOTHING""",
                        row["user_id"], row["balance"]
                    )
                print(f"[MIGRATION] Flagged {len(rows)} existing user(s) with wager requirement.")

            await conn.execute(
                "INSERT INTO bot_settings (key, value) VALUES ('migration_wager_req_done', 'true') "
                "ON CONFLICT (key) DO NOTHING"
            )
        finally:
            await release_conn(conn)
    except Exception as e:
        print(f"[MIGRATION] Error: {e}")

async def get_conn():
    """Acquire a connection from the pool. Waits up to 10s for pool to be ready."""
    if _pool is None:
        for _ in range(20):
            await asyncio.sleep(0.5)
            if _pool is not None:
                break
        if _pool is None:
            raise RuntimeError("Database is still starting up. Please try again in a moment.")
    return await _pool.acquire()

async def release_conn(conn):
    """Release connection back to pool."""
    await _pool.release(conn)

@bot.event
async def on_guild_join(guild: discord.Guild):
    await ensure_bot_role(guild)
    await ensure_rank_roles(guild)
    await ensure_staff_role(guild)
    await ensure_member_role(guild)
    await _setup_guild_channels(guild)
    print(f"[BOT] Joined new guild: {guild.name} — roles and channels set up")

@bot.event
async def on_invite_create(invite: discord.Invite):
    """Keep cache up to date when new invites are created."""
    if invite.guild:
        _invite_cache.setdefault(invite.guild.id, {})[invite.code] = invite.uses or 0

@bot.event
async def on_invite_delete(invite: discord.Invite):
    """Remove deleted invites from cache."""
    if invite.guild:
        _invite_cache.get(invite.guild.id, {}).pop(invite.code, None)

@bot.event
async def on_member_join(member: discord.Member):
    asyncio.create_task(on_member_join_raid_check(member))
    if not member.bot:
        conn = await get_conn()
        try:
            await _ensure_member_snapshot_table(conn)
            await _snapshot_member(conn, member)
        except Exception:
            pass
        finally:
            await release_conn(conn)
    guild = member.guild

    conn = await get_conn()
    try:
        await ensure_user(conn, member)
        row = await get_user(conn, member.id)
        if row and row["wagered"] >= 1:
            await update_user_rank(member, row["wagered"])
    finally:
        await release_conn(conn)

    await asyncio.sleep(1)
    inviter_id = None
    try:
        try:
            current_invites = await guild.invites()
        except discord.Forbidden:
            print(f"[INVITE] Missing MANAGE_GUILD permission in {guild.name}")
            current_invites = []
        except Exception as e:
            print(f"[INVITE] Could not fetch invites: {e}")
            current_invites = []

        old_counts = _invite_cache.get(guild.id, {})
        if not old_counts and current_invites:
            _invite_cache[guild.id] = {inv.code: (inv.uses or 0) for inv in current_invites}
            print(f"[INVITE] Cache was empty — populated, skipping join ({member.name})")
        elif current_invites:
            for inv in sorted(current_invites, key=lambda x: (x.uses or 0) - old_counts.get(x.code, 0), reverse=True):
                old   = old_counts.get(inv.code, 0)
                delta = (inv.uses or 0) - old
                if delta > 0 and inv.inviter and inv.inviter.id != member.id and not inv.inviter.bot:
                    inviter_id = str(inv.inviter.id)
                    print(f"[INVITE] {member.name} joined via {inv.code} by {inv.inviter.name}")
                    break
            _invite_cache[guild.id] = {inv.code: (inv.uses or 0) for inv in current_invites}
    except Exception as e:
        print(f"[INVITE] Error tracking invite: {e}")

    unverified_role = await ensure_unverified_role(guild)
    if unverified_role and unverified_role not in member.roles:
        try:
            await member.add_roles(unverified_role, reason="Auto-assigned Unverified role on join")
        except Exception as e:
            print(f"[INVITE] Could not assign Unverified role to {member}: {e}")

    if inviter_id:
        conn = await get_conn()
        try:
            already = await conn.fetchrow(
                "SELECT invitee_id FROM invite_rewards WHERE invitee_id=$1", str(member.id))
            pending = await conn.fetchrow(
                "SELECT member_id FROM pending_verifications WHERE member_id=$1", str(member.id))
            if not already and not pending:
                await conn.execute(
                    """
                    INSERT INTO pending_verifications (member_id, guild_id, inviter_id, joined_at)
                    VALUES ($1, $2, $3, $4)
                    ON CONFLICT (member_id) DO UPDATE SET inviter_id=$3, joined_at=$4
                    """,
                    str(member.id), str(guild.id), inviter_id, now_ts()
                )
                print(f"[INVITE] Stored pending invite: {member.name} invited by {inviter_id} — awaiting Member role")
        except Exception as e:
            print(f"[INVITE] Could not store pending invite: {e}")
        finally:
            await release_conn(conn)

@bot.event
async def on_member_update(before: discord.Member, after: discord.Member):
    """Pay invite reward when the invited user gains the Member role."""
    had_member = any(r.name == MEMBER_ROLE_NAME for r in before.roles)
    has_member  = any(r.name == MEMBER_ROLE_NAME for r in after.roles)
    if had_member or not has_member:
        return

    conn = await get_conn()
    try:
        pending = await conn.fetchrow(
            "SELECT inviter_id FROM pending_verifications WHERE member_id=$1",
            str(after.id)
        )
        if not pending or not pending["inviter_id"]:
            return

        inviter_id = pending["inviter_id"]

        await conn.execute(
            "DELETE FROM pending_verifications WHERE member_id=$1", str(after.id)
        )

        suspended = await conn.fetchrow(
            "SELECT 1 FROM suspended_invite_rewards WHERE user_id=$1", inviter_id)
        already = await conn.fetchrow(
            "SELECT invitee_id FROM invite_rewards WHERE invitee_id=$1", str(after.id))
        if suspended or already:
            return

        setting = await conn.fetchrow("SELECT value FROM bot_settings WHERE key='invite_reward'")
        reward  = int(setting["value"]) if setting else 0
        if reward <= 0:
            return

        guild       = after.guild
        inviter_obj = guild.get_member(int(inviter_id)) or await bot.fetch_user(int(inviter_id))
        if not inviter_obj:
            return

        await ensure_user(conn, inviter_obj)
        await update_balance(conn, int(inviter_id), reward)
        await log_transaction(conn, int(inviter_id), "invite_reward", reward,
                              f"invited {after.name} (Member role confirmed)")
        await add_wager_req(conn, int(inviter_id), reward, "invite_reward")
        await conn.execute(
            """INSERT INTO invite_rewards (invitee_id, inviter_id, rewarded_at, reward_amt, wagered_so_far, req_met)
               VALUES ($1, $2, $3, $4, 0, FALSE) ON CONFLICT (invitee_id) DO NOTHING""",
            str(after.id), inviter_id, now_ts(), reward
        )
        print(f"[INVITE] Paid reward to {inviter_obj} ({format_amount(reward)}) — {after.name} received Member role")

        log_e = discord.Embed(
            title="✦  Invite Reward Triggered",
            description=(
                f"**{after.name}** received the Member role\n"
                f"{inviter_obj.mention} earned **{format_amount(reward)}** 💎"
            ),
            color=C_WIN
        )
        log_e.add_field(name="👤 Inviter",  value=f"{inviter_obj.mention}\n`{inviter_obj}`", inline=True)
        log_e.add_field(name="🆕 Invitee", value=f"{after.mention}\n`{after}`",              inline=True)
        log_e.add_field(name="💎 Reward",  value=f"**{format_amount(reward)} 💎**",             inline=True)
        _brand_embed(log_e)
        await send_invite_log(log_e)

        try:
            dm = discord.Embed(
                title="🎉  Invite Reward!",
                description=(
                    f"**{after.name}** just got the Member role and you earned\n"
                    f"**{format_amount(reward)} 💎**!\n\nKeep inviting to earn more 👑"
                ),
                color=C_WIN
            )
            _brand_embed(dm)
            await inviter_obj.send(embed=dm)
        except Exception:
            pass

    except Exception as e:
        print(f"[INVITE] on_member_update error: {e}")
    finally:
        await release_conn(conn)

async def send_invite_log(embed: discord.Embed):
    """Send to the invite rewards log channel (set via /setinvitelog → INVITE_LOG_ID global)."""
    if not INVITE_LOG_ID:
        print("[INVITE LOG] No channel set — use /setinvitelog")
        return
    ch = bot.get_channel(INVITE_LOG_ID)
    if ch is None:
        try:
            ch = await bot.fetch_channel(INVITE_LOG_ID)
        except Exception as e:
            print(f"[INVITE LOG] Could not fetch channel {INVITE_LOG_ID}: {e}")
            return
    try:
        await ch.send(embed=embed)
    except discord.Forbidden:
        print(f"[INVITE LOG] Missing send permission in #{ch.name}")
    except Exception as e:
        print(f"[INVITE LOG] Failed to send: {e}")

async def send_reward_log(embed: discord.Embed):
    """Send to the rewards log channel (rain, promo, daily, boost — set via /setrewardlog)."""
    if not REWARD_LOG_ID:
        return
    ch = bot.get_channel(REWARD_LOG_ID)
    if ch is None:
        try:
            ch = await bot.fetch_channel(REWARD_LOG_ID)
        except Exception as e:
            print(f"[REWARD LOG] Could not fetch channel {REWARD_LOG_ID}: {e}")
            return
    try:
        await ch.send(embed=embed)
    except Exception as e:
        print(f"[REWARD LOG] Failed to send: {e}")

async def send_log(embed: discord.Embed):
    """Send to the game results log channel."""
    if not LOG_CHANNEL_ID:
        return
    ch = bot.get_channel(LOG_CHANNEL_ID)
    if ch is None:
        try:
            ch = await bot.fetch_channel(LOG_CHANNEL_ID)
        except Exception as e:
            print(f"[GAME LOG] Could not fetch channel {LOG_CHANNEL_ID}: {e}")
            return
    try:
        await ch.send(embed=embed)
    except discord.Forbidden:
        print(f"[GAME LOG] Missing send permission in #{ch.name}")
    except Exception as e:
        print(f"[GAME LOG] Failed to send: {e}")

async def send_finance_log(embed: discord.Embed):
    """Send to the deposits/withdrawals/gem changes log channel."""
    ch = bot.get_channel(FINANCE_LOG_ID)
    if ch is None:
        try:
            ch = await bot.fetch_channel(FINANCE_LOG_ID)
        except Exception as e:
            print(f"[FINANCE LOG] Could not fetch channel {FINANCE_LOG_ID}: {e}")
            return
    try:
        await ch.send(embed=embed)
    except discord.Forbidden:
        print(f"[FINANCE LOG] Missing send permission in #{ch.name}")
    except Exception as e:
        print(f"[FINANCE LOG] Failed to send: {e}")

async def send_tip_log(embed: discord.Embed):
    """Send to BOTH admin tip-log AND the public tipping channel in Extra."""
    if TIP_LOG_ID:
        ch = bot.get_channel(TIP_LOG_ID)
        if ch is None:
            try: ch = await bot.fetch_channel(TIP_LOG_ID)
            except Exception: ch = None
        if ch:
            try: await ch.send(embed=embed)
            except Exception as e: print(f"[TIP LOG] admin send failed: {e}")
    if TIP_PUBLIC_LOG_ID:
        pub = bot.get_channel(TIP_PUBLIC_LOG_ID)
        if pub is None:
            try: pub = await bot.fetch_channel(TIP_PUBLIC_LOG_ID)
            except Exception: pub = None
        if pub:
            try:
                sender = next((f.value for f in embed.fields if "From" in f.name), "Someone")
                recip  = next((f.value for f in embed.fields if "To"   in f.name), "Someone")
                amount = next((f.value for f in embed.fields if "Amount" in f.name), "?")
                pub_e  = discord.Embed(color=0xA855F7,
                    description=f"💸 **Tip Sent!**\n**From:** {sender}\n**To:** {recip}\n**Amount:** {amount} 💎")
                pub_e.set_footer(text=now_ts())
                await pub.send(embed=pub_e)
            except Exception as e: print(f"[TIP LOG] public send failed: {e}")

async def send_vouches_log(embed: discord.Embed):
    """Send to the public vouches channel (deposits, withdrawals, big wins)."""
    if not VOUCHES_CHANNEL_ID:
        return
    ch = bot.get_channel(VOUCHES_CHANNEL_ID)
    if ch is None:
        try:
            ch = await bot.fetch_channel(VOUCHES_CHANNEL_ID)
        except Exception as e:
            print(f"[VOUCHES] Could not fetch channel {VOUCHES_CHANNEL_ID}: {e}")
            return
    try:
        await ch.send(embed=embed)
    except Exception as e:
        print(f"[VOUCHES] Failed to send: {e}")

def admin_only():
    async def predicate(interaction: discord.Interaction) -> bool:
        if interaction.guild:
            authed = is_admin(interaction.user)
        else:
            authed = await is_admin_user(interaction.user)
        if not authed:
            await interaction.response.send_message(
                "❌ You need the **Admin** role.", ephemeral=True)
            return False
        return True
    return app_commands.check(predicate)

def owner_only():
    """Restrict to server owner or Owner role."""
    async def predicate(interaction: discord.Interaction) -> bool:
        if not interaction.guild:
            await interaction.response.send_message(
                "❌ This command can only be used in a server.", ephemeral=True)
            return False
        is_owner = (
            interaction.user.id == interaction.guild.owner_id or
            any(r.name == OWNER_ROLE_NAME for r in interaction.user.roles)
        )
        if is_owner:
            return True
        await interaction.response.send_message(
            "❌ You need the **Owner** role.", ephemeral=True)
        return False
    return app_commands.check(predicate)

@bot.tree.command(name="link", description="Link your Roblox account to show your avatar on all game embeds.")
@app_commands.describe(username="Your Roblox username")
async def cmd_link(interaction: discord.Interaction, username: str):
    await interaction.response.defer(ephemeral=True)
    username = username.strip()

    try:
        import aiohttp
        async with aiohttp.ClientSession() as session:
            async with session.post(
                "https://users.roblox.com/v1/usernames/users",
                json={"usernames": [username], "excludeBannedUsers": True}
            ) as resp:
                if resp.status != 200:
                    await interaction.followup.send(
                        "❌ Could not reach Roblox. Try again in a moment.", ephemeral=True)
                    return
                data = await resp.json()
                if not data.get("data"):
                    await interaction.followup.send(
                        f"❌ Roblox user **{username}** not found. Check the spelling.", ephemeral=True)
                    return
                roblox_user = data["data"][0]
                roblox_id   = roblox_user["id"]
                roblox_name = roblox_user["name"]

            async with session.get(
                f"https://thumbnails.roblox.com/v1/users/avatar-headshot"
                f"?userIds={roblox_id}&size=420x420&format=Png&isCircular=false"
            ) as resp:
                avatar_url = None
                if resp.status == 200:
                    tdata = await resp.json()
                    avatar_url = tdata["data"][0]["imageUrl"] if tdata.get("data") else None
    except Exception as e:
        print(f"[ROBLOX] Link error: {e}")
        await interaction.followup.send("❌ Roblox API error. Try again later.", ephemeral=True)
        return

    conn = await get_conn()
    try:
        await conn.execute("""
            INSERT INTO roblox_links (user_id, roblox_username, roblox_id, linked_at)
            VALUES ($1, $2, $3, $4)
            ON CONFLICT (user_id) DO UPDATE
            SET roblox_username=$2, roblox_id=$3, linked_at=$4
        """, str(interaction.user.id), roblox_name, roblox_id, now_ts())
    finally:
        await release_conn(conn)

    _roblox_avatar_cache.pop(interaction.user.id, None)

    embed = discord.Embed(
        title=None,
        description=(
            f"## 🔗  LINKED\n"
            f"**{roblox_name}** is now connected to your account.\n"
            f"`ID: {roblox_id}`\n\n"
            f"─────────────────────────────\n"
            f"Your Roblox avatar will appear on all game embeds.\n"
            f"You can now use all bloxysab commands! ✦"
        ),
        color=C_GOLD
    )
    if avatar_url:
        embed.set_thumbnail(url=avatar_url)
    _brand_embed(embed)
    await interaction.followup.send(embed=embed, ephemeral=True)

@bot.tree.command(name="balance", description="View your balance and stats.")
async def cmd_balance(interaction: discord.Interaction):
    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        row = await get_user(conn, interaction.user.id)
        if not row:
            await interaction.response.send_message("⚠️  Could not load your data.", ephemeral=True)
            return
        balance  = row["balance"]
        wagered  = row["wagered"]
        wins     = row["wins"]
        losses   = row["losses"]
        streak   = row["streak"]
        max_streak = row["max_streak"]
    except Exception as e:
        print(f"[ERROR] balance: {type(e).__name__}: {e}")
        await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
        return
    finally:
        await release_conn(conn)

    net_profit = balance - wagered
    pnl_sign   = "+" if net_profit >= 0 else "-"

    profit_str = f"+{format_amount(abs(net_profit))}" if net_profit >= 0 else f"-{format_amount(abs(net_profit))}"
    embed = discord.Embed(
        color=C_GOLD,
        title=f"💎  {interaction.user.display_name}'s Balance",
        description=(
            f"💰 Balance: **{format_amount(balance)}** 💎\n"
            f"🎲 Wagered: **{format_amount(wagered)}** 💎\n"
            f"📉 Profit: **{profit_str}** 💎\n"
            f"\n"
            f"Use /deposit to obtain balance\n"
            f"Use /stock to view items available for withdraw\n"
            f"5M ≈ 40M–50M/s"
        )
    )
    embed.set_thumbnail(url=await get_avatar(interaction.user))
    _brand_embed(embed)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="unlock", description="Stuck in a game? Use this to unlock yourself.")
async def cmd_unlock(interaction: discord.Interaction):
    uid = interaction.user.id
    if uid in _active_games:
        _end_game_session(uid)
        await interaction.response.send_message(
            "🔓 You've been unlocked! You can play games again.",
            ephemeral=True
        )
    else:
        await interaction.response.send_message(
            "✅ You're not locked — you can already play games.",
            ephemeral=True
        )


@bot.tree.command(name="rank", description="View your wagering rank and progress.")
async def cmd_rank(interaction: discord.Interaction):
    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        row = await get_user(conn, interaction.user.id)
    except Exception as e:
        print(f"[ERROR] rank: {type(e).__name__}: {e}")
        await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
        return
    finally:
        await release_conn(conn)

    if not row:
        await interaction.response.send_message("❌ Could not load your profile. Try again.", ephemeral=True)
        return

    wagered = row["wagered"]
    emoji, name, low, high, color = get_rank(wagered)

    display_emoji, display_name, display_color = emoji, name, color

    is_max     = (high == math.inf)
    next_label = "MAX RANK" if is_max else format_amount(high)
    need_str   = "" if is_max else f"  ·  Need **{format_amount(max(0, high - wagered))}** more"
    bar_str    = progress_bar(1, 1) if is_max else progress_bar(wagered - low, high - low)
    pct        = 100 if is_max else round(min((wagered - low) / max(high - low, 1) * 100, 100), 1)

    embed = discord.Embed(
        color=display_color,
        description=(
            f"## {display_emoji}  {display_name.upper()}\n"
            f"{interaction.user.mention}\n"
            f"─────────────────────────────\n"
            f"**Wagered** `{format_amount(wagered)}`\n"
            f"**Next Rank** `{next_label}`{need_str}\n"
            f"`{bar_str}` {pct:.0f}%"
        )
    )
    embed.set_thumbnail(url=await get_avatar(interaction.user))
    _brand_embed(embed)
    await interaction.response.send_message(embed=embed)

@bot.tree.command(name="ranks", description="View all ranks and their wager requirements.")
async def cmd_ranks(interaction: discord.Interaction):
    """Show all wager-based ranks and the two leaderboard-only roles."""
    lines = []
    for low, high, emoji, name, color in RANK_DATA:
        req = format_amount(low) if low > 0 else "Starting rank"
        if high >= 10**17:
            next_txt = ""
        else:
            next_txt = f" → {format_amount(high)}"
        lines.append(f"{emoji} **{name}** — `{req}`{next_txt}")

    lb_lines = [
        f"👑 **Champion** — 🏅 **#1** on the wagered leaderboard",
        f"💎 **Diamond Whale** — 🥈🥉 **#2 & #3** on the wagered leaderboard",
    ]

    embed = discord.Embed(
        color=C_GOLD,
        title="✦  Sabpot — All Ranks",
        description=(
            "**Wager Ranks** — earned by wagering gems\n"
            "─────────────────────────────\n"
            + "\n".join(lines)
            + "\n\n**Leaderboard Roles** — assigned hourly, not shown in /rank\n"
            "─────────────────────────────\n"
            + "\n".join(lb_lines)
        )
    )
    _brand_embed(embed)
    await interaction.response.send_message(embed=embed)

@bot.tree.command(name="leaderboard", description="Top 10 players by balance or total wagered.")
@app_commands.describe(sort="What to rank by")
@app_commands.choices(sort=[
    app_commands.Choice(name="Balance", value="balance"),
    app_commands.Choice(name="Wagered", value="wagered"),
])
async def cmd_leaderboard(interaction: discord.Interaction, sort: str = "wagered"):
    await interaction.response.defer()
    sort_col = "wagered" if sort not in ("balance", "wagered") else sort
    conn = await get_conn()
    try:
        rows = await conn.fetch(
            f"SELECT user_id, balance, wagered FROM users ORDER BY {sort_col} DESC LIMIT 10"
        )
    except Exception as e:
        print(f"[ERROR] leaderboard: {type(e).__name__}: {e}")
        await interaction.followup.send("⚠️  Something went wrong — try again.", ephemeral=True)
        return
    finally:
        await release_conn(conn)

    if not rows:
        await interaction.followup.send("No players yet!", ephemeral=True)
        return

    def _lb_embed(lb_rows, lb_sort):
        MEDAL  = {0: "🥇", 1: "🥈", 2: "🥉"}
        BOLT   = "⚡"
        lines  = []
        for i, r in enumerate(lb_rows):
            rank_e, _, _, _, _ = get_rank(r["wagered"])
            val  = format_amount(r[lb_sort])
            if i in MEDAL:
                lines.append(f"{MEDAL[i]} {rank_e} <@{r['user_id']}> • **{val}**")
            else:
                lines.append(f"#{i+1} {BOLT} <@{r['user_id']}> • **{val}**")
        lbl = "Balance" if lb_sort == "balance" else "Total Wager"
        e   = discord.Embed(
            color=C_GOLD,
            title=f"🎰  Leaderboard - {lbl}",
            description="\n".join(lines)
        )
        e.set_footer(text=f"SABFlippy • Use /rank to check your stats | Today at {datetime.now(timezone.utc).strftime('%H:%M')}")
        _brand_embed(e)
        return e

    class _LBView(discord.ui.View):
        def __init__(self, cur):
            super().__init__(timeout=60)
            self.cur = cur
            self._sync()
        def _sync(self):
            self.btn_bal.style = discord.ButtonStyle.blurple if self.cur == "balance" else discord.ButtonStyle.grey
            self.btn_wag.style = discord.ButtonStyle.blurple if self.cur == "wagered" else discord.ButtonStyle.grey
        async def on_timeout(self):
            for item in self.children:
                item.disabled = True

        @discord.ui.button(label="Balance")
        async def btn_bal(self, itx, btn):
            self.cur = "balance"; self._sync()
            c2 = await get_conn()
            try: r2 = await c2.fetch("SELECT user_id,balance,wagered FROM users ORDER BY balance DESC LIMIT 10")
            finally: await release_conn(c2)
            await itx.response.edit_message(embed=_lb_embed(r2, "balance"), view=self)
        @discord.ui.button(label="Wagered")
        async def btn_wag(self, itx, btn):
            self.cur = "wagered"; self._sync()
            c2 = await get_conn()
            try: r2 = await c2.fetch("SELECT user_id,balance,wagered FROM users ORDER BY wagered DESC LIMIT 10")
            finally: await release_conn(c2)
            await itx.response.edit_message(embed=_lb_embed(r2, "wagered"), view=self)

    if not rows:
        await interaction.followup.send("No players yet!", ephemeral=True)
        return
    await interaction.followup.send(embed=_lb_embed(rows, sort_col), view=_LBView(sort_col))

@bot.tree.command(name="daily", description="Claim your daily gem bonus based on your rank.")
async def cmd_daily(interaction: discord.Interaction):
    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            row = await get_user(conn, interaction.user.id)

            claim_row = await conn.fetchrow(
                "SELECT last_claim FROM daily_claims WHERE user_id=$1", str(interaction.user.id)
            )
            now_dt  = datetime.now(timezone.utc)
            now_str = now_dt.strftime("%Y-%m-%d %H:%M:%S UTC")

            if claim_row and claim_row["last_claim"]:
                try:
                    raw = claim_row["last_claim"].replace(" UTC", "")
                    last_dt = datetime.strptime(raw, "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)
                    diff    = now_dt - last_dt
                    if diff.total_seconds() < 86400:
                        remaining = timedelta(seconds=86400) - diff
                        hrs, rem  = divmod(int(remaining.total_seconds()), 3600)
                        mins      = rem // 60
                        await interaction.response.send_message(
                            f"⏳ Already claimed! Your next daily is in **{hrs}h {mins}m** — see you then!",
                            ephemeral=True
                        )
                        return
                except (ValueError, TypeError):
                    pass

            wagered = row["wagered"] if row else 0
            emoji, rank_name, _, _, color = get_rank(wagered)
            reward = random.randint(DAILY_MIN, DAILY_MAX)

            await update_balance(conn, interaction.user.id, reward)
            await log_transaction(conn, interaction.user.id, "daily", reward, rank_name)
            await add_wager_req(conn, interaction.user.id, reward, "daily")
            try:
                await update_quest_progress(conn, interaction.user.id, "daily", "any", 1, bet=0)
            except Exception as _qe:
                print(f"[QUESTS] daily error: {_qe}")
            await conn.execute(
                """INSERT INTO daily_claims (user_id, last_claim) VALUES ($1, $2)
                   ON CONFLICT (user_id) DO UPDATE SET last_claim=$2""",
                str(interaction.user.id), now_str
            )
            new_bal = (await get_user(conn, interaction.user.id))["balance"]
        finally:
            await release_conn(conn)

    emoji, rank_name, _, _, color = get_rank(wagered)
    embed = discord.Embed(
        color=C_WIN,
        description=(
            f"## 🎁  DAILY BONUS\n"
            f"{interaction.user.mention}  ·  {emoji} **{rank_name}**\n"
            f"╔══════════════════════╗\n"
            f"║  + {format_amount(reward):>19}  ║\n"
            f"║  bal  {format_amount(new_bal):>16}  ║\n"
            f"╚══════════════════════╝"
        )
    )
    embed.set_thumbnail(url=await get_avatar(interaction.user))
    _brand_embed(embed)

    await interaction.response.send_message(embed=embed)

@bot.tree.command(name="tip", description="Send gems to another user.")
@app_commands.describe(user="Who to tip", amount="Amount e.g. 5k, 1M")
async def cmd_tip(interaction: discord.Interaction, user: discord.Member, amount: str):
    if user.id == interaction.user.id:
        await interaction.response.send_message("❌ Cannot tip yourself.", ephemeral=True)
        return
    if user.bot:
        await interaction.response.send_message("❌ Cannot tip a bot.", ephemeral=True)
        return

    amt = parse_amount(amount)
    if not amt or amt <= 0:
        await interaction.response.send_message("❌ Invalid amount.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            await ensure_user(conn, user)

            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                sender_row = await get_user(conn, interaction.user.id)
                bal = sender_row["balance"] if sender_row else 0
                await interaction.response.send_message(
                    f"❌ You only have **{format_amount(bal)}**. Need **{format_amount(amt)}**.",
                    ephemeral=True)
                return

            await update_balance(conn, user.id, amt)
            await conn.execute(
                "UPDATE users SET tips_sent=tips_sent+$1 WHERE user_id=$2", amt, str(interaction.user.id)
            )
            await conn.execute(
                "UPDATE users SET tips_recv=tips_recv+$1 WHERE user_id=$2", amt, str(user.id)
            )
            await log_transaction(conn, interaction.user.id, "tip_sent", -amt, f"to {user.id}")
            await log_transaction(conn, user.id, "tip_recv", amt, f"from {interaction.user.id}")
            await add_wager_req(conn, user.id, amt, "tip_recv")  # recipient must wager tip before withdrawing
            try:
                await update_quest_progress(conn, interaction.user.id, "tip", "any", 1, bet=0)
            except Exception as _qe:
                print(f"[QUESTS] tip error: {_qe}")

            sender_row = await get_user(conn, interaction.user.id)
            recv_row   = await get_user(conn, user.id)
            sender_bal = sender_row["balance"] if sender_row else 0
            recv_bal   = recv_row["balance"]   if recv_row   else 0
            sender_wager = sender_row["wagered"] if sender_row else 0
        finally:
            await release_conn(conn)

    embed = discord.Embed(
        color=C_WIN,
        description=(
            f"## 💸  Tip Sent\n"
            f"**{interaction.user.display_name}** → **{user.display_name}**\n"
            f"Amount: **{format_amount(amt)} 💎**"
        )
    )
    embed.add_field(name="Your Balance",  value=f"**{format_amount(sender_bal)}** 💎", inline=True)
    embed.add_field(name="Their Balance", value=f"**{format_amount(recv_bal)}** 💎",   inline=True)
    _brand_embed(embed)
    await interaction.response.send_message(embed=embed)

    log_e = discord.Embed(color=0xF59E0B, title="💸 Tip Transaction")
    log_e.add_field(name="From",   value=f"{interaction.user.mention} `{interaction.user.id}`", inline=True)
    log_e.add_field(name="To",     value=f"{user.mention} `{user.id}`",                         inline=True)
    log_e.add_field(name="Amount", value=format_amount(amt),                                     inline=True)
    log_e.add_field(name="New Balances",
                    value=f"{interaction.user.mention}: **{format_amount(sender_bal)}**\n{user.mention}: **{format_amount(recv_bal)}**",
                    inline=False)
    log_e.add_field(name="Wager Req Added",
                    value=f"{user.mention} must wager **{format_amount(amt)}**",
                    inline=False)
    log_e.set_footer(text=now_ts())
    await send_tip_log(log_e)

async def _get_unlocked(conn, user_id: int) -> list[str]:
    """Return list of achievement IDs the user has unlocked."""
    rows = await conn.fetch(
        "SELECT achievement FROM achievements WHERE user_id=$1",
        str(user_id)
    )
    return [r["achievement"] for r in rows]

async def _get_user_stats(conn, user_id: int) -> dict:
    """Return per-game stats dict for achievement checks."""
    row = await conn.fetchrow("SELECT * FROM user_stats WHERE user_id=$1", str(user_id))
    if not row:
        return {}
    return dict(row)

def _build_ach_display(unlocked: list[str]) -> str:
    """Build a compact list of unlocked achievements."""
    if not unlocked:
        return "_No achievements yet — keep playing!_"
    lines = []
    for a in ACHIEVEMENTS:
        if a["id"] in unlocked:
            lines.append(f"{a['emoji']} **{a['name']}** — {a['desc']}")
    if not lines:
        return "_No achievements yet — keep playing!_"
    display = lines[:10]
    if len(unlocked) > 10:
        display.append(f"_...and {len(unlocked) - 10} more_")
    return "\n".join(display)

async def check_and_grant_achievements(conn, user_id: int, row) -> None:
    """Check all achievements and grant any newly earned ones."""
    extra = await _get_user_stats(conn, user_id)
    already = set(await _get_unlocked(conn, user_id))
    for a in ACHIEVEMENTS:
        if a["id"] in already:
            continue
        try:
            earned = a["check"](row, extra)
        except Exception:
            earned = False
        if earned:
            try:
                await conn.execute(
                    """INSERT INTO achievements (user_id, achievement, unlocked_at)
                       VALUES ($1, $2, $3) ON CONFLICT DO NOTHING""",
                    str(user_id), a["id"], now_ts()
                )
            except Exception as e:
                print(f"[ACHIEVEMENTS] grant error {a['id']}: {e}")

@bot.tree.command(name="stats", description="View gambling statistics.")
@app_commands.describe(user="User to check (leave empty for yourself)")
async def cmd_stats(interaction: discord.Interaction, user: Optional[discord.Member] = None):
    await interaction.response.defer()
    try:
        target = user or interaction.user
        conn = await get_conn()
        try:
            await ensure_user(conn, target)
            row      = await get_user(conn, target.id)
            unlocked = await _get_unlocked(conn, target.id)
        finally:
            await release_conn(conn)

        total_g  = row["wins"] + row["losses"]
        win_rate = (row["wins"] / total_g * 100) if total_g > 0 else 0
        emoji, rank_name, _, _, color = get_rank(row["wagered"])

        net     = row['balance'] - row['wagered']
        net_str = f"+{format_amount(net)}" if net >= 0 else f"-{format_amount(abs(net))}"
        bar_filled = int(win_rate / 10)
        wr_bar  = "█" * bar_filled + "░" * (10 - bar_filled)

        total_ach = len(ACHIEVEMENTS)
        done_ach  = len(unlocked)

        embed = discord.Embed(
            color=color,
            description=(
                f"## {emoji}  {target.display_name.upper()}\n"
                f"{rank_name}\n"
                f"─────────────────────────────\n"
                f"**Gems** `{format_amount(row['balance'])}`  ·  **Wagered** `{format_amount(row['wagered'])}`\n"
                f"**P&L** `{net_str}`  ·  **Record** `{row['wins']}W {row['losses']}L ({win_rate:.1f}%)`\n"
                f"**Best Streak** `{row['max_streak']}`\n"
                f"**Tips Out** `{format_amount(row['tips_sent'])}`  ·  **Tips In** `{format_amount(row['tips_recv'])}`"
            )
        )
        embed.set_thumbnail(url=await get_avatar(target))
        embed.add_field(
            name=f"🏅  Achievements  {done_ach}/{total_ach}",
            value=_build_ach_display(unlocked),
            inline=False
        )
        _brand_embed(embed)
        await interaction.followup.send(embed=embed)
    except Exception as e:
        import traceback; traceback.print_exc()
        print(f"[ERROR] stats: {type(e).__name__}: {e}")
        try:
            await interaction.followup.send("⚠️  Something went wrong — try again.", ephemeral=True)
        except Exception:
            pass

@bot.tree.command(name="history", description="View your last 10 transactions.")
async def cmd_history(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        rows = await conn.fetch(
            "SELECT action, amount, note, ts FROM transactions WHERE user_id=$1 ORDER BY id DESC LIMIT 10",
            str(interaction.user.id)
        )
    finally:
        await release_conn(conn)

    if not rows:
        await interaction.followup.send("📋 No transactions yet.", ephemeral=True)
        return

    _ACT_ICONS = {
        "daily": "🎁", "tip_sent": "💸", "tip_recv": "💰", "rain_recv": "🌧️",
        "rain_host": "🌧️", "rain_refund": "🔄", "promo_redeem": "🎟️",
        "addcoins": "➕", "removecoins": "➖", "rakeback": "💹",
        "invite_reward": "🔗", "coinflip": "🪙", "dice": "🎲",
        "roulette": "◉", "blackjack": "♠️", "baccarat": "🎴",
        "mines": "💣", "scratch": "🎟️", "hilo": "🃏", "towers": "🏰",
        "war": "⚔️", "rps": "✊", "horserace": "🏇", "upgrader": "⬆️",
    }
    lines = []
    for r in rows:
        icon  = _ACT_ICONS.get(r["action"], "•")
        sign  = "+" if r["amount"] >= 0 else ""
        ts    = r["ts"][:16]
        lines.append(f"{icon} `{ts}`  **{sign}{format_amount(r['amount'])}**  _{r['action']}_")
    embed = discord.Embed(title="📋  Recent Transactions", description="\n".join(lines), color=C_GOLD)
    _brand_embed(embed)

    await interaction.followup.send(embed=embed, ephemeral=True)

@bot.tree.command(name="createpromocode", description="[Admin] Create a redeemable promo code.")
@app_commands.describe(
    code="The promo code (e.g. SUMMER2025)",
    amount="Gems each redeem gives e.g. 5M",
    max_uses="How many times it can be redeemed"
)
@admin_only()
async def cmd_createpromocode(interaction: discord.Interaction, code: str, amount: str, max_uses: int):
    amt = parse_amount(amount)
    if not amt or amt <= 0:
        await interaction.response.send_message("❌ Invalid amount.", ephemeral=True)
        return
    if max_uses <= 0:
        await interaction.response.send_message("❌ Max uses must be at least 1.", ephemeral=True)
        return

    code = code.upper().strip()
    conn = await get_conn()
    try:
        existing = await conn.fetchrow("SELECT code FROM promocodes WHERE code=$1", code)
        if existing:
            await interaction.response.send_message(f"❌ Code `{code}` already exists.", ephemeral=True)
            return
        await conn.execute(
            "INSERT INTO promocodes (code, amount, max_uses, created_by) VALUES ($1, $2, $3, $4)",
            code, amt, max_uses, str(interaction.user.id)
        )
    finally:
        await release_conn(conn)

    embed = discord.Embed(title="Promo Code Created", color=C_WIN)
    embed.add_field(name="Code",      value=f"`{code}`",             inline=True)
    embed.add_field(name="Amount",    value=format_amount(amt),      inline=True)
    embed.add_field(name="Max Uses",  value=str(max_uses),           inline=True)
    embed.set_footer(text=f"Created by {interaction.user.display_name}")
    await interaction.response.send_message(embed=embed)

    log_e = discord.Embed(title="🎟️ Promo Code Created", color=C_WIN)
    log_e.add_field(name="Code",     value=f"`{code}`",        inline=True)
    log_e.add_field(name="Amount",   value=format_amount(amt), inline=True)
    log_e.add_field(name="Max Uses", value=str(max_uses),      inline=True)
    log_e.add_field(name="Creator",  value=interaction.user.mention, inline=True)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

@bot.tree.command(name="redeemcode", description="Redeem a promo code for gems.")
@app_commands.describe(code="The promo code to redeem")
async def cmd_redeemcode(interaction: discord.Interaction, code: str):
    code = code.upper().strip()
    conn = await get_conn()
    amt = new_uses = new_bal = row = None
    try:
        await ensure_user(conn, interaction.user)
        row = await conn.fetchrow("SELECT * FROM promocodes WHERE code=$1", code)

        if not row:
            await interaction.response.send_message("❌ Invalid promo code.", ephemeral=True)
            return
        if not row["active"]:
            await interaction.response.send_message("❌ This code is no longer active.", ephemeral=True)
            return
        if row["uses"] >= row["max_uses"]:
            await interaction.response.send_message("❌ This code has reached its maximum uses.", ephemeral=True)
            return

        already = await conn.fetchrow(
            "SELECT 1 FROM promocode_redeems WHERE code=$1 AND user_id=$2",
            code, str(interaction.user.id)
        )
        if already:
            await interaction.response.send_message("❌ You've already redeemed this code.", ephemeral=True)
            return

        amt = row["amount"]

        updated = await conn.execute(
            "UPDATE promocodes SET uses=uses+1 WHERE code=$1 AND uses<max_uses",
            code
        )
        if updated == "UPDATE 0":
            await interaction.response.send_message("❌ This code has reached its maximum uses.", ephemeral=True)
            return

        inserted = await conn.execute(
            "INSERT INTO promocode_redeems (code, user_id) VALUES ($1, $2) ON CONFLICT DO NOTHING",
            code, str(interaction.user.id)
        )
        if inserted == "INSERT 0":
            await conn.execute("UPDATE promocodes SET uses=uses-1 WHERE code=$1", code)
            await interaction.response.send_message("❌ You've already redeemed this code.", ephemeral=True)
            return

        new_uses = row["uses"] + 1
        await update_balance(conn, interaction.user.id, amt)
        await log_transaction(conn, interaction.user.id, "promo_redeem", amt, code)
        await add_wager_req(conn, interaction.user.id, amt, "promo_redeem")
        if new_uses >= row["max_uses"]:
            await conn.execute("UPDATE promocodes SET active=FALSE WHERE code=$1", code)

        user_row = await get_user(conn, interaction.user.id)
        new_bal  = user_row["balance"] if user_row else 0
    except Exception as e:
        print(f"[ERROR] redeemcode: {type(e).__name__}: {e}")
        if not interaction.response.is_done():
            await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
        return
    finally:
        await release_conn(conn)

    if amt is None or row is None:
        return

    embed = discord.Embed(
        color=C_WIN,
        description=(
            f"## 🎟️  CODE REDEEMED\n"
            f"**`{code}`** — **{format_amount(amt)} 💎** added\n"
            f"╔══════════════════════╗\n"
            f"║  Gems  {format_amount(new_bal):>15}  ║\n"
            f"╚══════════════════════╝\n"
            f"Uses remaining: **{row['max_uses'] - new_uses}**"
        )
    )
    _brand_embed(embed)
    await interaction.response.send_message(embed=embed)

    log_e = discord.Embed(title="🎟️ Promo Code Redeemed", color=C_GOLD)
    log_e.add_field(name="User",   value=interaction.user.mention, inline=True)
    log_e.add_field(name="Code",   value=f"`{code}`",              inline=True)
    log_e.add_field(name="Amount", value=format_amount(amt),       inline=True)
    log_e.add_field(name="Uses",   value=f"{new_uses}/{row['max_uses']}", inline=True)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

class BaseGameView(discord.ui.View):
    """
    All game Views inherit from this.
    on_error() catches any unhandled exception in a button callback,
    logs it, and always sends a visible error response so the user
    is never left with a stuck "thinking" spinner.
    Automatically clears the user's active game session on stop/timeout.
    """
    def stop(self):
        creator = getattr(self, 'creator', None)
        if creator:
            _end_game_session(creator.id)
        super().stop()

    async def on_timeout(self):
        creator = getattr(self, 'creator', None)
        if creator:
            _end_game_session(creator.id)

    async def on_error(self, interaction: discord.Interaction,
                       error: Exception, item) -> None:
        import traceback
        label = getattr(item, 'label', None) or getattr(item, 'custom_id', str(item))
        print(f"[GAME ERROR] {self.__class__.__name__} / {label}: {type(error).__name__}: {error}")
        traceback.print_exc()
        creator = getattr(self, 'creator', None)
        if creator:
            _end_game_session(creator.id)
        self.stop()
        msg = "❌ Something went wrong. Your bet has been refunded if it was deducted."
        try:
            if interaction.response.is_done():
                await interaction.followup.send(msg, ephemeral=True)
            else:
                await interaction.response.send_message(msg, ephemeral=True)
        except Exception as send_err:
            print(f"[GAME ERROR] Failed to send error message: {send_err}")


class RainView(discord.ui.View):
    def __init__(self, host: discord.User, total: int, end_time: float, secs: int):
        super().__init__(timeout=secs + 10)  # +10s buffer so view stays alive until rain ends
        self.host      = host
        self.total     = total
        self.end_time  = end_time
        self.joiners:  set[int] = set()
        self.ended     = False
        self._lock     = asyncio.Lock()
        self._msg      = None

    @discord.ui.button(label="🌧️ Join Rain", style=discord.ButtonStyle.blurple)
    async def join_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if self.ended:
            await interaction.response.send_message("❌ This rain has already ended.", ephemeral=True)
            return
        if interaction.user.id == self.host.id:
            await interaction.response.send_message("❌ You can't join your own rain.", ephemeral=True)
            return
        async with self._lock:
            if interaction.user.id in self.joiners:
                await interaction.response.send_message("✅ You're already in this rain!", ephemeral=True)
            else:
                self.joiners.add(interaction.user.id)
                await interaction.response.send_message("🌧️ You joined the rain!", ephemeral=True)

@bot.tree.command(name="createrain", description="[Admin] Split gems between everyone who joins.")
@app_commands.describe(
    amount="Total amount to rain e.g. 10M",
    duration="How long to accept joins e.g. 30m, 1h, 2h"
)
@admin_only()
async def cmd_createrain(interaction: discord.Interaction, amount: str, duration: str):
    amt = parse_amount(amount)
    if not amt or amt <= 0:
        await interaction.response.send_message("❌ Invalid amount.", ephemeral=True)
        return

    secs = parse_duration(duration)
    if not secs:
        await interaction.response.send_message(
            "❌ Invalid duration. Use `30m`, `1h`, `2h` etc.", ephemeral=True)
        return
    if secs > 86400:
        await interaction.response.send_message("❌ Maximum duration is 24 hours.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
        finally:
            await release_conn(conn)

    if not deducted:
        conn = await get_conn()
        try:
            host_row = await get_user(conn, interaction.user.id)
            bal = host_row["balance"] if host_row else 0
        finally:
            await release_conn(conn)
        await interaction.response.send_message(
            f"❌ You only have **{format_amount(bal)}**. Need **{format_amount(amt)}**.",
            ephemeral=True)
        return

    dur_label = format_duration(secs)
    end_time  = time.time() + secs
    view      = RainView(interaction.user, amt, end_time, secs)

    embed = discord.Embed(
        color=C_BLUE,
        description=(
            f"## 🌧️  GEM DROP\n"
            f"**{interaction.user.mention}** is dropping **{format_amount(amt)} 💎**!\n"
            f"─────────────────────────────\n"
            f"Hit the button below to claim your share.\n"
            f"Ends in **{dur_label}**."
        )
    )
    embed.set_footer(text=f"0 joined  ·  {dur_label} remaining")
    await interaction.response.send_message(embed=embed, view=view)
    msg       = await interaction.original_response()
    view._msg = msg

    async def run_rain():
        elapsed          = 0
        update_interval  = min(30, secs // 2) if secs > 10 else secs
        while elapsed < secs:
            sleep_time = min(update_interval, secs - elapsed)
            await asyncio.sleep(sleep_time)
            elapsed += sleep_time
            remaining = secs - elapsed
            if remaining > 0:
                count = len(view.joiners)
                try:
                    upd = discord.Embed(
                        title="🌧️  IT'S RAINING GEMS!",
                        description=(
                            f"**{interaction.user.mention}** is raining **{format_amount(amt)} 💎**!\
\
"
                            "Click the button to join and get your share!\
"
                            f"Rain ends in **{format_duration(int(remaining))}**."
                        ),
                        color=C_BLUE
                    )
                    upd.set_footer(text=f"{count} joined • {format_duration(int(remaining))} remaining")
                    await msg.edit(embed=upd, view=view)
                except Exception as e:

                    print(f"[ERROR] {type(e).__name__}: {e}")
                    pass

        view.ended = True
        view.stop()

        joiners = list(view.joiners)
        if not joiners:
            conn = await get_conn()
            try:
                await update_balance(conn, interaction.user.id, amt)
                await log_transaction(conn, interaction.user.id, "rain_refund", amt,
                                      "nobody joined")
            finally:
                await release_conn(conn)
            ended = discord.Embed(
                title="🌧️  RAIN ENDED",
                description=f"**Prize:** {format_amount(amt)} 💎\
\
Nobody joined — gems refunded to host.",
                color=C_PUSH
            )
            ended.set_footer(text=f"Hosted by {interaction.user.display_name} • {now_ts()}")
            try:
                await msg.edit(embed=ended, view=None)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
            return

        share = amt // len(joiners)
        if share <= 0:
            share = 1

        conn = await get_conn()
        try:
            await log_transaction(conn, interaction.user.id, "rain_host", -amt,
                                  f"rain to {len(joiners)} users")
            for uid in joiners:
                member = interaction.guild.get_member(uid) if interaction.guild else None
                if member:
                    await ensure_user(conn, member)
                await update_balance(conn, uid, share)
                await log_transaction(conn, uid, "rain_recv", share, f"rain by {interaction.user.id}")
                await conn.execute(
                    """INSERT INTO user_stats (user_id, rain_count) VALUES ($1, 1)
                       ON CONFLICT (user_id) DO UPDATE SET rain_count = user_stats.rain_count + 1""",
                    str(uid)
                )
                await add_wager_req(conn, uid, share, "rain_recv")
        finally:
            await release_conn(conn)

        mentions = " ".join(f"<@{uid}>" for uid in joiners)
        ended = discord.Embed(
            title="🌧️  RAIN ENDED",
            description=(
                f"**{format_amount(amt)} 💎** split between **{len(joiners)}** people!\
"
                f"Each received **{format_amount(share)} 💎**"
            ),
            color=C_WIN
        )
        ended.set_footer(text=f"Hosted by {interaction.user.display_name} • {now_ts()}")
        try:
            await msg.edit(embed=ended, view=None)
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass
        try:
            await msg.channel.send(
                f"🌧️ Rain winners: {mentions}\
Each received **{format_amount(share)} 💎**!")
        except Exception as e:
            print(f"[RAIN] Could not send announcement: {e}")

        log_e = discord.Embed(title="🌧️ Rain Distributed", color=C_BLUE)
        log_e.add_field(name="Host",       value=interaction.user.mention, inline=True)
        log_e.add_field(name="Total",      value=format_amount(amt),       inline=True)
        log_e.add_field(name="Recipients", value=str(len(joiners)),        inline=True)
        log_e.add_field(name="Per Person", value=format_amount(share),     inline=True)
        log_e.set_footer(text=now_ts())
        await send_finance_log(log_e)

    asyncio.create_task(run_rain())

@bot.tree.command(name="games", description="Browse all games and their payouts.")
async def cmd_games(interaction: discord.Interaction):
    _GAMES = {
        "classic": {
            "title": "🎲  CLASSIC GAMES",
            "color": C_BLUE,
            "fields": [
                ("🪙  Coinflip",    "Pick **Heads** or **Tails** — win **2×** your bet."),
                ("🎲  Dice",        "Roll higher than your opponent. Tie = full refund. Play vs bot or a friend."),
                ("⚔️  War",         "Draw a card — highest card wins **2×**. Tie = both get refunded."),
                ("✊  RPS",          "Rock · Paper · Scissors. Chain wins up to **1.96×**. Cash out any round."),
                ("◉  Roulette",     "🔴 Red/🔵 Blue → **2×**  ·  🟡 Yellow → **6×**  ·  Provably fair spins."),
            ]
        },
        "cards": {
            "title": "♠️  CARD GAMES",
            "color": C_GOLD,
            "fields": [
                ("♠️  Blackjack",     "Beat the dealer to **21**. Natural BJ pays **2.5×**. Double down available."),
                ("🎲  Blackjack Dice","Same rules as BJ but rolled with dice. Natural = **2.5×**."),
                ("🎴  Baccarat",      "Closest to **9** wins. Player/Banker pays **1:1**  ·  Tie pays **8:1**."),
                ("🃏  HiLo",          "Guess Higher or Lower each card. Chain correct guesses to multiply. Cash out anytime."),
            ]
        },
        "arcade": {
            "title": "🎮  ARCADE GAMES",
            "color": C_VIP,
            "fields": [
                ("💣  Mines",        "5×5 grid. Reveal gems, dodge bombs. Cash out at any point. Up to **5,000×**."),
                ("🏰  Towers",       "Climb **10** rows — 2 safe tiles, 1 bomb each row. Higher = bigger multiplier."),
                ("⬆️  Upgrader",     "Set a target multiplier (1.2× minimum). Beat the odds and walk away bigger."),
                ("🎈  Balloon",      "Each pump adds **+25%** but burst chance grows. Don't pop it!"),
                ("🎰  Slots",        "Spin 3 reels — match symbols. Up to **50×** on triple 7s."),
                ("🎲  Color Dice",   "Pick a color. Roll 6 dice. 2+ matches = refund  ·  1 match = **2×**  ·  0 = lose."),
            ]
        },
        "other": {
            "title": "🎉  OTHER GAMES",
            "color": C_WIN,
            "fields": [
                ("🎟️  Scratch Card", "Scratch 9 tiles — match 3 to win. Top prize: **30×** 👑"),
                ("🏇  Horse Race",   "Back one of 4 horses in a live animated race. Win = **3.76×** payout."),
                ("⚔️  Case Battles", "Open cases head-to-head. Highest total value wins the whole pot."),
            ]
        },
    }

    def _games_embed(key):
        p = _GAMES[key]
        e = discord.Embed(
            title=p["title"],
            color=p["color"]
        )
        for name, val in p["fields"]:
            e.add_field(name=name, value=val, inline=False)
        _brand_embed(e)
        return e

    class _GamesView(discord.ui.View):
        def __init__(self):
            super().__init__(timeout=120)
            self.cur = "classic"
            self._sync()
        def _sync(self):
            self.b_cls.style = discord.ButtonStyle.blurple if self.cur=="classic" else discord.ButtonStyle.grey
            self.b_crd.style = discord.ButtonStyle.blurple if self.cur=="cards"   else discord.ButtonStyle.grey
            self.b_arc.style = discord.ButtonStyle.blurple if self.cur=="arcade"  else discord.ButtonStyle.grey
            self.b_oth.style = discord.ButtonStyle.blurple if self.cur=="other"   else discord.ButtonStyle.grey
        async def on_timeout(self):
            for item in self.children:
                item.disabled = True

        @discord.ui.button(label="🎲 Classic", style=discord.ButtonStyle.blurple)
        async def b_cls(self, itx, btn):
            self.cur="classic"; self._sync()
            await itx.response.edit_message(embed=_games_embed("classic"), view=self)
        @discord.ui.button(label="♠️ Cards", style=discord.ButtonStyle.grey)
        async def b_crd(self, itx, btn):
            self.cur="cards"; self._sync()
            await itx.response.edit_message(embed=_games_embed("cards"), view=self)
        @discord.ui.button(label="🎮 Arcade", style=discord.ButtonStyle.grey)
        async def b_arc(self, itx, btn):
            self.cur="arcade"; self._sync()
            await itx.response.edit_message(embed=_games_embed("arcade"), view=self)
        @discord.ui.button(label="🎉 Other", style=discord.ButtonStyle.grey)
        async def b_oth(self, itx, btn):
            self.cur="other"; self._sync()
            await itx.response.edit_message(embed=_games_embed("other"), view=self)

    await interaction.response.send_message(embed=_games_embed("classic"), view=_GamesView())

def parse_duration(text: str) -> Optional[int]:
    text = text.strip().lower()
    units = {"m": 60, "h": 3600, "d": 86400}
    if not text or text[-1] not in units:
        return None
    try:
        amount = float(text[:-1])
        return int(amount * units[text[-1]]) if amount > 0 else None
    except ValueError:
        return None

def format_duration(seconds: int) -> str:
    if seconds >= 86400:
        d = seconds // 86400
        return f"{d} day{'s' if d != 1 else ''}"
    if seconds >= 3600:
        h = seconds // 3600
        return f"{h} hour{'s' if h != 1 else ''}"
    m = max(seconds // 60, 1)
    return f"{m} minute{'s' if m != 1 else ''}"

def _giveaway_active_embed(prize: int, dur_label: str, end_str: str,
                            host_mention: str, count: int, remaining_secs: int) -> discord.Embed:
    remaining_str = format_duration(remaining_secs)
    e = discord.Embed(
        color=C_GOLD,
        description=(
            f"## 🎉  GIVEAWAY\n"
            f"╔══════════════════════╗\n"
            f"║  Prize  {format_amount(prize):>14}  ║\n"
            f"╚══════════════════════╝\n"
            f"**Host:** {host_mention}  ·  **Ends:** {end_str}\n"
            f"Press **Enter Giveaway** to join. Press again to leave."
        )
    )
    e.set_footer(text=f"{count} {'entry' if count == 1 else 'entries'}  ·  Ends in {remaining_str}")
    return e

class GiveawayView(discord.ui.View):
    """Persistent view — button works after restarts because custom_id includes giveaway DB id."""

    def __init__(self, giveaway_id: int):
        super().__init__(timeout=None)
        self.giveaway_id = giveaway_id
        self.enter_button.custom_id = f"giveaway_enter_{giveaway_id}"

    @discord.ui.button(label="🎉 Enter Giveaway", style=discord.ButtonStyle.green,
                       custom_id="giveaway_enter_placeholder")
    async def enter_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.defer(ephemeral=True)
        conn = await get_conn()
        try:
            row = await conn.fetchrow(
                "SELECT ended FROM giveaways WHERE id=$1", self.giveaway_id)
            if not row or row["ended"]:
                await interaction.followup.send("❌ This giveaway has already ended.", ephemeral=True)
                return

            existing = await conn.fetchrow(
                "SELECT 1 FROM giveaway_entrants WHERE giveaway_id=$1 AND user_id=$2",
                self.giveaway_id, str(interaction.user.id))

            if existing:
                await conn.execute(
                    "DELETE FROM giveaway_entrants WHERE giveaway_id=$1 AND user_id=$2",
                    self.giveaway_id, str(interaction.user.id))
                await interaction.followup.send("✅ You left the giveaway.", ephemeral=True)
            else:
                await conn.execute(
                    "INSERT INTO giveaway_entrants (giveaway_id, user_id) VALUES ($1, $2) "
                    "ON CONFLICT DO NOTHING",
                    self.giveaway_id, str(interaction.user.id))
                await interaction.followup.send("🎉 You entered the giveaway! Good luck!", ephemeral=True)
        finally:
            await release_conn(conn)

async def _finish_giveaway(giveaway_id: int):
    """Pick a winner, pay them, update the message. Safe to call after a restart."""
    conn = await get_conn()
    try:
        row = await conn.fetchrow("SELECT * FROM giveaways WHERE id=$1", giveaway_id)
        if not row or row["ended"]:
            return

        entrant_rows = await conn.fetch(
            "SELECT user_id FROM giveaway_entrants WHERE giveaway_id=$1", giveaway_id)
        entrants = [r["user_id"] for r in entrant_rows]

        await conn.execute("UPDATE giveaways SET ended=TRUE WHERE id=$1", giveaway_id)

        prize     = row["prize"]
        host_id   = int(row["host_id"])
        host_name = row["host_name"]
        channel   = bot.get_channel(int(row["channel_id"]))
        msg       = None
        if channel:
            try:
                msg = await channel.fetch_message(int(row["message_id"]))
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass

        if not entrants:
            await update_balance(conn, int(row["host_id"]), prize)
            await log_transaction(conn, int(row["host_id"]), "giveaway_refund", prize,
                                  f"nobody entered giveaway #{giveaway_id}")
            ended_embed = discord.Embed(
                title="🎊  GIVEAWAY ENDED",
                description=f"**Prize:** {format_amount(prize)} 💎\
\
No one entered — gems refunded to host.",
                color=C_PUSH
            )
            ended_embed.set_footer(text=f"Hosted by {host_name} • {now_ts()}")
            if msg:
                try:
                    await msg.edit(embed=ended_embed, view=None)
                except Exception as e:

                    print(f"[ERROR] {type(e).__name__}: {e}")
                    pass
            return

        winner_id  = int(random.choice(entrants))
        guild      = channel.guild if channel else None
        winner     = guild.get_member(winner_id) if guild else None
        winner_mention = winner.mention if winner else f"<@{winner_id}>"

        if winner:
            await ensure_user(conn, winner)
        await update_balance(conn, winner_id, prize)
        await log_transaction(conn, winner_id, "giveaway_win", prize, f"giveaway #{giveaway_id}")
        new_bal = (await get_user(conn, winner_id))["balance"]

    finally:
        await release_conn(conn)

    ended_embed = discord.Embed(
        title="🏆  GIVEAWAY WINNER",
        description=(
            f"**Prize:** {format_amount(prize)} 💎\
"
            f"**Winner:** {winner_mention}\
"
            f"**Entries:** {len(entrants)}\
\
"
            f"🏆 Congratulations! **{format_amount(prize)}** has been added to your balance!"
        ),
        color=C_WIN
    )
    ended_embed.set_footer(text=f"Hosted by {host_name} • {now_ts()}")

    if msg:
        try:
            await msg.edit(embed=ended_embed, view=None)
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass
        try:
            await msg.channel.send(
                f"🎉 Congratulations {winner_mention}! "
                f"You won **{format_amount(prize)} 💎** from the giveaway!"
            )
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass

    if winner:
        try:
            await winner.send(embed=discord.Embed(
                title="🏆  YOU WON",
                description=(
                    f"You won **{format_amount(prize)} 💎** in a giveaway "
                    f"hosted by **{host_name}**!\
"
                    f"New balance: **{format_amount(new_bal)}**"
                ),
                color=C_WIN
            ))
        except Exception:
            pass

    log_e = discord.Embed(title="🎉 Giveaway Ended", color=C_WIN)
    log_e.add_field(name="Host",    value=f"<@{host_id}>",       inline=True)
    log_e.add_field(name="Winner",  value=winner_mention,         inline=True)
    log_e.add_field(name="Prize",   value=format_amount(prize),   inline=True)
    log_e.add_field(name="Entries", value=str(len(entrants)),     inline=True)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

async def _run_giveaway_timer(giveaway_id: int, secs_remaining: float,
                               prize: int, dur_label: str, end_str: str,
                               host_mention: str, msg: discord.Message,
                               view: "GiveawayView"):
    """Background timer task — updates embed every 30s then calls _finish_giveaway."""
    elapsed = 0
    update_interval = 30
    total = secs_remaining

    while elapsed < total:
        sleep_time = min(update_interval, total - elapsed)
        await asyncio.sleep(sleep_time)
        elapsed += sleep_time

        remaining = total - elapsed
        if remaining > 0:
            conn = await get_conn()
            try:
                count = await conn.fetchval(
                    "SELECT COUNT(*) FROM giveaway_entrants WHERE giveaway_id=$1", giveaway_id)
            finally:
                await release_conn(conn)
            try:
                await msg.edit(
                    embed=_giveaway_active_embed(prize, dur_label, end_str,
                                                 host_mention, count, int(remaining)),
                    view=view
                )
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass

    await _finish_giveaway(giveaway_id)

async def _restore_ticket_views():
    """Called on_ready — re-registers persistent WithdrawTicketView for all pending tickets
    so buttons keep working after a bot restart."""
    try:
        conn = await get_conn()
        try:
            rows = await conn.fetch(
                "SELECT id, user_id, channel_id FROM withdrawals_queue WHERE status='pending'"
            )
        finally:
            await release_conn(conn)
        for row in rows:
            try:
                ticket_id = row["id"]
                user_id   = int(row["user_id"])
                view      = WithdrawTicketView(ticket_id=ticket_id, user_id=user_id)
                bot.add_view(view)
            except Exception as e:
                print(f"[TICKETS] Could not restore view for ticket {row['id']}: {e}")
        if rows:
            print(f"[TICKETS] Restored {len(rows)} pending ticket view(s)")
    except Exception as e:
        print(f"[TICKETS] Restore error: {e}")

async def restore_giveaways():
    """Called on_ready — resumes timers for any active giveaways that survived a restart."""
    conn = await get_conn()
    try:
        rows = await conn.fetch("SELECT * FROM giveaways WHERE ended=FALSE")
    finally:
        await release_conn(conn)

    now = time.time()
    for row in rows:
        giveaway_id = row["id"]
        remaining   = row["end_time"] - now

        channel = bot.get_channel(int(row["channel_id"]))
        if not channel:
            continue
        try:
            msg = await channel.fetch_message(int(row["message_id"]))
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            asyncio.create_task(_finish_giveaway(giveaway_id))
            continue

        view = GiveawayView(giveaway_id)
        bot.add_view(view, message_id=int(row["message_id"]))

        host_mention = f"<@{row['host_id']}>"

        if remaining <= 0:
            asyncio.create_task(_finish_giveaway(giveaway_id))
        else:
            asyncio.create_task(_run_giveaway_timer(
                giveaway_id, remaining,
                row["prize"], row["dur_label"], row["end_str"],
                host_mention, msg, view
            ))
            print(f"[GIVEAWAY] Restored giveaway #{giveaway_id} — {format_duration(int(remaining))} remaining")

@bot.tree.command(name="giveaway", description="[Admin] Start a gem giveaway.")
@app_commands.describe(
    prize="Prize amount e.g. 5M, 1B",
    duration="Duration e.g. 1m, 2h, 1d, 7d"
)
@admin_only()
async def cmd_giveaway(interaction: discord.Interaction, prize: str, duration: str):
    amt = parse_amount(prize)
    if not amt or amt <= 0:
        await interaction.response.send_message("❌ Invalid prize amount.", ephemeral=True)
        return

    secs = parse_duration(duration)
    if not secs:
        await interaction.response.send_message(
            "❌ Invalid duration. Use `1m`, `2h`, `1d`, `7d` etc.", ephemeral=True)
        return
    if secs > 86400 * 7:
        await interaction.response.send_message("❌ Maximum duration is 7 days.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if deducted:
                await log_transaction(conn, interaction.user.id, "giveaway_host", -amt,
                                      f"giveaway prize")
        finally:
            await release_conn(conn)

    if not deducted:
        conn = await get_conn()
        try:
            host_row = await get_user(conn, interaction.user.id)
            bal = host_row["balance"] if host_row else 0
        finally:
            await release_conn(conn)
        await interaction.response.send_message(
            f"❌ You only have **{format_amount(bal)}**. Need **{format_amount(amt)}** for this giveaway.",
            ephemeral=True)
        return

    end_time  = time.time() + secs
    dur_label = format_duration(secs)
    end_dt    = datetime.now(timezone.utc) + timedelta(seconds=secs)
    end_str   = end_dt.strftime("%Y-%m-%d %H:%M UTC")
    host_name = interaction.user.display_name

    conn = await get_conn()
    try:
        giveaway_id = await conn.fetchval(
            """INSERT INTO giveaways
               (channel_id, message_id, host_id, host_name, prize, end_time, dur_label, end_str)
               VALUES ($1, $2, $3, $4, $5, $6, $7, $8)
               RETURNING id""",
            str(interaction.channel_id), "0",
            str(interaction.user.id), host_name,
            amt, end_time, dur_label, end_str
        )
    finally:
        await release_conn(conn)

    view = GiveawayView(giveaway_id)

    embed = _giveaway_active_embed(amt, dur_label, end_str,
                                    interaction.user.mention, 0, secs)
    await interaction.response.send_message(embed=embed, view=view)
    msg = await interaction.original_response()

    conn = await get_conn()
    try:
        await conn.execute(
            "UPDATE giveaways SET message_id=$1 WHERE id=$2",
            str(msg.id), giveaway_id
        )
    finally:
        await release_conn(conn)

    bot.add_view(view, message_id=msg.id)

    asyncio.create_task(_run_giveaway_timer(
        giveaway_id, secs, amt, dur_label, end_str,
        interaction.user.mention, msg, view
    ))

class CoinflipView(BaseGameView):
    def __init__(self, creator, bet, choice):
        super().__init__(timeout=120)
        self.creator            = creator
        self.bet                = bet
        self.choice             = choice
        self.opponent           = None
        self.vs_bot             = False
        self.started            = False
        self._join_lock         = asyncio.Lock()
        self._original_message  = None  # set after send

    @discord.ui.button(label="Join", style=discord.ButtonStyle.green, emoji="🤝")
    async def join_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id == self.creator.id:
            await interaction.response.send_message("❌ Can't join your own game.", ephemeral=True)
            return
        async with self._join_lock:
            if self.opponent or self.vs_bot:
                await interaction.response.send_message("❌ Game already has an opponent.", ephemeral=True)
                return

        await interaction.response.defer()

        async with self._join_lock:
            async with get_user_lock(interaction.user.id):
                conn = await get_conn()
                try:
                    await ensure_user(conn, interaction.user)
                    deducted = await deduct_balance_safe(conn, interaction.user.id, self.bet)
                    if not deducted:
                        row = await get_user(conn, interaction.user.id)
                        bal = row["balance"] if row else 0
                        await interaction.followup.send(
                            f"❌ Need **{format_amount(self.bet)}** to join. You have **{format_amount(bal)}**.",
                            ephemeral=True)
                        return
                    self.opponent = interaction.user
                finally:
                    await release_conn(conn)

        await interaction.followup.send(f"✅ {interaction.user.mention} joined! Creator press **Start**.")

    @discord.ui.button(label="vs Bot", style=discord.ButtonStyle.blurple, emoji="🤖")
    async def bot_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Only the creator can do this.", ephemeral=True)
            return
        async with self._join_lock:
            if self.opponent or self.vs_bot:
                await interaction.response.send_message("❌ Already has an opponent.", ephemeral=True)
                return
            self.vs_bot = True
        await interaction.response.defer()
        try:
            vsbot_embed = discord.Embed(
                title="🪙  Coinflip — Flipping...",
                color=C_GOLD,
                description=(
                    f"💰  Bet: **{format_amount(self.bet)}** 💎\n"
                    f"🎯  Side: **{self.choice}**\n\n"
                    f"🤖 Bot joined! Press **Start** to flip."
                )
            )
            _brand_embed(vsbot_embed)
            await interaction.edit_original_response(embed=vsbot_embed, view=self)
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass

    @discord.ui.button(label="Start", style=discord.ButtonStyle.red, emoji="▶")
    async def start_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Only creator can start.", ephemeral=True)
            return
        if not self.opponent and not self.vs_bot:
            await interaction.response.send_message("❌ Need an opponent first.", ephemeral=True)
            return
        if self.started:
            return

        await interaction.response.defer()
        self.started = True
        await self._resolve(interaction)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.started:
            try:
                await self._original_message.edit(
                    embed=discord.Embed(color=C_DARK, description="## 🪙  COIN FLIP — EXPIRED\n> Timed out — bet refunded"),
                    view=None)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
            conn = await get_conn()
            try:
                await update_balance(conn, self.creator.id, self.bet)
                if self.opponent:
                    await update_balance(conn, self.opponent.id, self.bet)
            finally:
                await release_conn(conn)
        await super().on_timeout()

    async def _resolve(self, interaction: discord.Interaction):
        if not interaction.response.is_done():
            await interaction.response.defer()
        msg = self._original_message

        if self.vs_bot:
            bot_wins    = random.random() < get_dynamic_house_win(self.creator.id)
            result      = ("Tails" if self.choice == "Heads" else "Heads") if bot_wins else self.choice
            creator_won = result == self.choice
        else:
            result      = random.choice(["Heads", "Tails"])
            creator_won = result == self.choice

        opponent_label = "🤖 Bot" if self.vs_bot else self.opponent.mention
        payout = min(self.bet * 2, MAX_PAYOUT) if creator_won else 0
        winner_mention = self.creator.mention if creator_won else opponent_label

        result_gif_url = COINFLIP_HEADS_GIF if result == "Heads" else COINFLIP_TAILS_GIF
        gif_url   = result_gif_url
        gif_valid = bool(
            gif_url and gif_url.startswith("http") and "PASTE_" not in gif_url
            and not gif_url.endswith("PASTE_HEADS_HERE.webp") and not gif_url.endswith("PASTE_TAILS_HERE.webp")
            and any(gif_url.lower().endswith(ext) for ext in (".gif", ".webp", ".png", ".jpg", ".jpeg"))
        )
        spin_gif_url = COINFLIP_SPINNING_GIF
        spin_gif_valid = bool(
            spin_gif_url and spin_gif_url.startswith("http") and "PASTE_" not in spin_gif_url
            and any(spin_gif_url.lower().endswith(ext) for ext in (".gif", ".webp", ".png", ".jpg", ".jpeg"))
        )
        spin_embed = discord.Embed(
            color=C_GOLD,
            description=(
                f"## 🪙  COINFLIP — FLIPPING...\n"
                f"┌─────────────────────────┐\n"
                f"│ 💰 **Bet** • {format_amount(self.bet)} 💎\n"
                f"│ 🎯 **Your Side** • {self.choice}\n"
                f"│ ⏳ **Flipping the coin...**\n"
                f"└─────────────────────────┘"
            )
        )
        if spin_gif_valid:
            spin_embed.set_image(url=spin_gif_url)
        elif gif_valid:
            spin_embed.set_image(url=gif_url)
        _brand_embed(spin_embed)
        try:
            await msg.edit(embed=spin_embed, view=None)
        except Exception as e:
            print(f"[COINFLIP ANIM] embed edit failed: {e}")
        await asyncio.sleep(2.5)

        try:
            conn = await get_conn()
            try:
                if creator_won:
                    payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "coinflip")
                    await record_game(conn, self.creator.id, True, self.bet, payout, "coinflip")
                    await log_transaction(conn, self.creator.id, "coinflip_win", payout - self.bet)
                    if not self.vs_bot and self.opponent:
                        await record_game(conn, self.opponent.id, False, self.bet, 0, "coinflip")
                        await log_transaction(conn, self.opponent.id, "coinflip_loss", -self.bet)
                else:
                    await record_game(conn, self.creator.id, False, self.bet, 0, "coinflip")
                    await log_transaction(conn, self.creator.id, "coinflip_loss", -self.bet)
                    if not self.vs_bot and self.opponent:
                        opponent_payout = min(self.bet * 2, MAX_PAYOUT)
                        opponent_payout = await apply_win_payout(conn, self.opponent.id, opponent_payout, self.bet, "coinflip")
                        await record_game(conn, self.opponent.id, True, self.bet, opponent_payout, "coinflip")
                        await log_transaction(conn, self.opponent.id, "coinflip_win", opponent_payout - self.bet)
                for uid, member_obj in [
                    (self.creator.id, interaction.guild.get_member(self.creator.id) if interaction.guild else None),
                    (self.opponent.id if self.opponent and not self.vs_bot else None,
                     interaction.guild.get_member(self.opponent.id) if self.opponent and not self.vs_bot and interaction.guild else None),
                ]:
                    if uid and member_obj:
                        row = await get_user(conn, uid)
                        if row:
                            await update_user_rank(member_obj, row["wagered"])
            finally:
                await release_conn(conn)
        except Exception as _db_err:
            print(f"[COINFLIP DB ERROR] {_db_err}")

        coin_icon = "🟡" if result == "Heads" else "⬛"
        if creator_won:
            result_color = C_WIN
            net          = payout - self.bet  # after-tax profit
            outcome_line = f"│ ✅ **You Win** • +{format_amount(net)} 💎"
        else:
            result_color = C_LOSS
            outcome_line = f"│ ❌ **You Lose** • -{format_amount(self.bet)} 💎"

        result_embed = discord.Embed(
            color=result_color,
            description=(
                f"## 🪙  COINFLIP — {result.upper()} {coin_icon}\n"
                f"┌─────────────────────────┐\n"
                f"│ 💰 **Bet** • {format_amount(self.bet)} 💎\n"
                f"│ 🎯 **Your Side** • {self.choice}\n"
                f"│ 🪙 **Result** • {result}\n"
                f"│ 🏆 **Winner** • {winner_mention}\n"
                f"{outcome_line}\n"
                f"└─────────────────────────┘"
            )
        )
        result_embed.set_thumbnail(url=await get_avatar(self.creator))
        if gif_valid:
            result_embed.set_image(url=gif_url)
        _brand_embed(result_embed)

        try:
            await msg.edit(embed=result_embed, view=None)
        except Exception as e:
            print(f"[COINFLIP RESULT] display failed: {e}")

        self.stop()
        log_e = discord.Embed(title="🪙 Coinflip Result", color=C_GOLD)
        log_e.add_field(name="Creator",  value=self.creator.mention,    inline=True)
        log_e.add_field(name="Opponent", value=opponent_label,          inline=True)
        log_e.add_field(name="Bet",      value=format_amount(self.bet), inline=True)
        log_e.add_field(name="Winner",   value=winner_mention,          inline=True)
        log_e.set_footer(text=now_ts())
        await send_log(log_e)

class ProgressiveCoinflipView(BaseGameView):
    def __init__(self, creator: discord.User, bet: int):
        super().__init__(timeout=120)
        self.creator         = creator
        self.initial_bet     = bet
        self.current_pot     = bet
        self.rounds          = 0
        self.done            = False
        self._original_message = None

    def game_embed(self, result_line: str = "", last_guess: str = "", last_result: str = "") -> discord.Embed:
        multiplier = self.current_pot / self.initial_bet
        color = C_GOLD if not result_line else (C_WIN if "✅" in result_line else C_LOSS)
        embed = discord.Embed(title="🪙  PROGRESSIVE FLIP", color=color)
        embed.add_field(name="💰 Initial Bet",   value=format_amount(self.initial_bet), inline=True)
        embed.add_field(name="💎 Current Pot",   value=format_amount(self.current_pot), inline=True)
        embed.add_field(name="📈 Multiplier",    value=f"{multiplier:.1f}x",            inline=True)
        embed.add_field(name="🔢 Rounds Won",    value=str(self.rounds),                inline=True)
        embed.add_field(name="⏭️ Next Win",      value=format_amount(self.current_pot * 2), inline=True)
        if last_guess and last_result:
            embed.add_field(name="Last Round", value=f"Guess: {last_guess} → Result: {last_result}", inline=False)
        if result_line:
            embed.add_field(name="Outcome", value=result_line, inline=False)
        embed.set_footer(text="Pick Heads or Tails — Cash out anytime to lock your winnings!")
        return embed

    async def _resolve_round(self, interaction: discord.Interaction, guess: str):
        if self.done:
            await interaction.response.send_message("❌ Game already over.", ephemeral=True)
            return

        await interaction.response.defer()

        bot_wins = random.random() < get_dynamic_house_win(self.creator.id, self.current_pot)
        if bot_wins:
            result = "Tails" if guess == "Heads" else "Heads"
        else:
            result = guess
        won = (result == guess)

        coin_gif     = COINFLIP_HEADS_GIF if result == "Heads" else COINFLIP_TAILS_GIF
        coin_gif     = coin_gif if (coin_gif and coin_gif.startswith("http") and "PASTE_" not in coin_gif and any(coin_gif.lower().endswith(ext) for ext in (".gif", ".webp", ".png", ".jpg", ".jpeg"))) else ""
        coin_icon    = "🟡" if result == "Heads" else "⬛"

        spin_gif_url   = COINFLIP_SPINNING_GIF
        spin_gif_valid = bool(
            spin_gif_url and spin_gif_url.startswith("http") and "PASTE_" not in spin_gif_url
            and any(spin_gif_url.lower().endswith(ext) for ext in (".gif", ".webp", ".png", ".jpg", ".jpeg"))
        )
        gif_valid = bool(coin_gif)
        spin_embed = discord.Embed(
            color=C_GOLD,
            description=(
                f"## 🪙  PROGRESSIVE COINFLIP — FLIPPING...\n"
                f"┌─────────────────────────┐\n"
                f"│ 💰 **Pot** • {format_amount(self.current_pot)} 💎\n"
                f"│ 🔄 **Round** • {self.rounds + 1}\n"
                f"│ ⏳ **Flipping the coin...**\n"
                f"└─────────────────────────┘"
            )
        )
        if spin_gif_valid:
            spin_embed.set_image(url=spin_gif_url)
        elif gif_valid:
            spin_embed.set_image(url=coin_gif)
        _brand_embed(spin_embed)
        try:
            await interaction.edit_original_response(embed=spin_embed)
        except Exception as e:
            print(f"[PCF ANIM] {e}")
        await asyncio.sleep(2.5)

        if won:
            self.rounds      += 1
            self.current_pot *= 2
            record_streak(self.creator.id, True, self.current_pot)
            win_embed = discord.Embed(
                color=C_WIN,
                description=(
                    f"# 🏆  CORRECT  🏆\n"
                    f"## {coin_icon}  {result.upper()}\n\n"
                    f"**Pot doubled → {format_amount(self.current_pot)}** 💎\n"
                    f"**Round {self.rounds}** complete — keep going or cash out!"
                )
            )
            if gif_valid:
                win_embed.set_image(url=coin_gif)
            _brand_embed(win_embed)
            try:
                await interaction.edit_original_response(embed=win_embed, view=self)
            except Exception as e:
                print(f"[PROG CF WIN] {e}")
        else:
            self.done = True
            self.stop()
            record_streak(self.creator.id, False, self.current_pot)
            lose_embed = discord.Embed(
                color=C_LOSS,
                description=(
                    f"# 💀  WRONG  💀\n"
                    f"## {coin_icon}  {result.upper()}\n\n"
                    f"**You lose {format_amount(self.current_pot)}** 💎\n"
                    f"You made it **{self.rounds}** round(s)."
                )
            )
            if gif_valid:
                lose_embed.set_image(url=coin_gif)
            _brand_embed(lose_embed)

            conn = await get_conn()
            try:
                await record_game(conn, self.creator.id, False, self.initial_bet, 0, "progressive_coinflip")
                await log_transaction(conn, self.creator.id, "progressive_coinflip", -self.initial_bet)
            finally:
                await release_conn(conn)

            try:
                await interaction.edit_original_response(embed=lose_embed, view=None)
            except Exception as e:
                print(f"[PROG CF LOSE] {e}")

            log_e = discord.Embed(title="🪙 Progressive Coinflip — Loss", color=C_LOSS)
            log_e.add_field(name="Player",  value=self.creator.mention,             inline=True)
            log_e.add_field(name="Bet",     value=format_amount(self.initial_bet),  inline=True)
            log_e.add_field(name="Rounds",  value=str(self.rounds),                 inline=True)
            log_e.set_footer(text=now_ts())
            await send_log(log_e)

    @discord.ui.button(label="Heads", style=discord.ButtonStyle.primary, emoji="🟡", row=0)
    async def heads_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._resolve_round(interaction, "Heads")

    @discord.ui.button(label="Tails", style=discord.ButtonStyle.secondary, emoji="🟣", row=0)
    async def tails_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._resolve_round(interaction, "Tails")

    @discord.ui.button(label="Cashout", style=discord.ButtonStyle.success, emoji="💰", row=1)
    async def cashout_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        if self.rounds == 0:
            await interaction.response.send_message("❌ You need to win at least 1 round before cashing out!", ephemeral=True)
            return
        if self.done:
            await interaction.response.send_message("❌ Game already over.", ephemeral=True)
            return

        await interaction.response.defer()
        self.done = True
        self.stop()

        payout = min(self.current_pot, MAX_PAYOUT)
        profit = payout - self.initial_bet
        record_streak(self.creator.id, True, payout)

        conn = await get_conn()
        try:
            payout = await apply_win_payout(conn, self.creator.id, payout, self.initial_bet, "progressive_coinflip")
            await record_game(conn, self.creator.id, True, self.initial_bet, payout, "progressive_coinflip")
            await log_transaction(conn, self.creator.id, "progressive_coinflip", profit)
            if interaction.guild:
                row = await get_user(conn, self.creator.id)
                member = interaction.guild.get_member(self.creator.id)
                if row and member:
                    await update_user_rank(member, row["wagered"])
        finally:
            await release_conn(conn)

        embed = discord.Embed(
            color=C_WIN,
            description=(
                f"## 💰  CASHED OUT\n"
                f"```diff\n"
                f"+ {format_amount(profit):>27}\n"
                f"  rounds  {self.rounds:>22}\n"
                f"  mult    {payout/self.initial_bet:>21.1f}x\n"
                f"```"
            )
        )
        embed.add_field(name="Wager",   value=f"`{format_amount(self.initial_bet)} 💎`", inline=True)
        embed.add_field(name="Payout",  value=f"`{format_amount(payout)} 💎`",           inline=True)
        embed.set_thumbnail(url=await get_avatar(self.creator))
        _brand_embed(embed)

        try:
            await interaction.edit_original_response(embed=embed, view=None)
        except Exception as e:
            print(f"[PROG CF CASHOUT] {e}")

        log_e = discord.Embed(title="🪙 Progressive Coinflip — Cashout", color=C_WIN)
        log_e.add_field(name="Player",  value=self.creator.mention,            inline=True)
        log_e.add_field(name="Bet",     value=format_amount(self.initial_bet), inline=True)
        log_e.add_field(name="Payout",  value=format_amount(payout),           inline=True)
        log_e.add_field(name="Rounds",  value=str(self.rounds),                inline=True)
        log_e.set_footer(text=now_ts())
        await send_log(log_e)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.done and self.rounds > 0:
            payout = min(self.current_pot, MAX_PAYOUT)
            conn = await get_conn()
            try:
                payout = await apply_win_payout(conn, self.creator.id, payout, self.initial_bet, "progressive_coinflip")
            finally:
                await release_conn(conn)
            try:
                await self._original_message.edit(
                    embed=discord.Embed(
                        title="Auto Cashed Out",
                        description=f"**{format_amount(payout)}** 💎 returned to your balance.",
                        color=C_PUSH),
                    view=None)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
        elif not self.done:
            conn = await get_conn()
            try:
                await super().on_timeout()
                await update_balance(conn, self.creator.id, self.initial_bet)
            finally:
                await release_conn(conn)
            try:
                await self._original_message.edit(
                    embed=discord.Embed(
                        title="Timed Out",
                        description=f"**{format_amount(self.initial_bet)}** 💎 refunded.",
                        color=C_PUSH),
                    view=None)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
        await super().on_timeout()

@bot.tree.command(name="progressivecoinflip", description="Double your pot each round — walk away before it's gone!")
@app_commands.describe(bet="Bet amount e.g. 100k, 1M")
async def cmd_progressivecoinflip(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("progressivecoinflip", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("progressivecoinflip", interaction.user):
        await interaction.response.send_message(
            "🔒 **Progressivecoinflip** is currently locked to staff only.", ephemeral=True
        )
        return
    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.", ephemeral=True)
                return
        finally:
            await release_conn(conn)

    pf   = pf_new_game()
    pf["game_name"] = "Progressive Coinflip"
    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view = ProgressiveCoinflipView(interaction.user, amt)
    view._pf_game_id = pf["game_id"]
    embed = view.game_embed()
    embed.add_field(name="🔐 Provably Fair", value=f"`{pf['commitment'][:32]}...` | ID: `{pf['game_id']}`", inline=False)
    await interaction.response.send_message(embed=embed, view=view)
    view._original_message = await interaction.original_response()

_active_dice_games: dict[int, "DiceGameState"] = {}

class DiceGameState:
    def __init__(self, creator, bet, mode: str, target: int):
        self.creator        = creator
        self.opponent       = None
        self.bet            = bet
        self.mode           = mode      # "normal" or "crazy"
        self.target         = target    # 1, 2, or 3
        self.score          = {creator.id: 0}
        self.lobby_msg      = None      # the public lobby message
        self.channel        = None
        self.waiting_roll   = set()     # who still needs to roll this round
        self.round_rolls    = {}        # {user_id: roll_value}
        self.round_num      = 0
        self.done           = False

    def pot(self) -> int:
        return self.bet * 2

    def score_line(self) -> str:
        if not self.opponent:
            return ""
        c_score = self.score.get(self.creator.id, 0)
        o_score = self.score.get(self.opponent.id, 0)
        return (
            f"**{self.creator.display_name}** {c_score} — "
            f"{o_score} **{self.opponent.display_name}**"
        )

    def lobby_embed(self) -> discord.Embed:
        mode_label = "🔼 Normal  ·  Highest roll wins" if self.mode == "normal" else "🔽 Crazy  ·  Lowest roll wins"
        e = discord.Embed(
            title="🎲  Dice Battle  ·  Open Lobby",
            color=C_GOLD,
            description=(
                f"**Host** » {self.creator.mention}\n"
                f"**Bet** » {format_amount(self.bet)}  ·  **Pot** » {format_amount(self.pot())}\n"
                f"**Mode** » {mode_label}\n"
                f"**First to** » {self.target} round{'s' if self.target > 1 else ''} wins\n\n"
                f"Press **Join** to enter the battle!"
            )
        )
        _brand_embed(e)
        return e

class DiceModeView(discord.ui.View):
    """Step 1 — pick Normal or Crazy."""
    def __init__(self, creator, bet, amt):
        super().__init__(timeout=60)
        self.creator = creator
        self.bet     = bet
        self.amt     = amt

    async def _pick_mode(self, interaction: discord.Interaction, mode: str):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        view = DiceTargetView(self.creator, self.bet, mode)
        mode_label = "🔼 Normal — highest roll wins" if mode == "normal" else "🔽 Crazy — lowest roll wins"
        e = discord.Embed(
            title="🎲  Dice Battle  ·  Pick Rounds",
            color=C_GOLD,
            description=(
                f"**Bet** » {format_amount(self.bet)}\n"
                f"**Mode** » {mode_label}\n\n"
                f"How many rounds does it take to win?\n"
                f"Choose **First to 1**, **2**, or **3** below."
            )
        )
        _brand_embed(e)
        await interaction.response.edit_message(embed=e, view=view)

    @discord.ui.button(label="Normal", style=discord.ButtonStyle.primary, emoji="🔼")
    async def normal_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._pick_mode(interaction, "normal")

    @discord.ui.button(label="Crazy", style=discord.ButtonStyle.danger, emoji="🔽")
    async def crazy_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._pick_mode(interaction, "crazy")

    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary, emoji="✖️")
    async def cancel_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        async with get_user_lock(self.creator.id):
            conn = await get_conn()
            try:
                await update_balance(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)
        _end_game_session(self.creator.id)
        e = discord.Embed(
            title="🎲  Dice  ·  Cancelled",
            color=C_DARK,
            description="Game cancelled. Your bet has been returned to your balance."
        )
        _brand_embed(e)
        await interaction.response.edit_message(embed=e, view=None)

class DiceTargetView(discord.ui.View):
    """Step 2 — pick first to 1 / 2 / 3."""
    def __init__(self, creator, bet, mode: str):
        super().__init__(timeout=60)
        self.creator = creator
        self.bet     = bet
        self.mode    = mode

    async def _pick_target(self, interaction: discord.Interaction, target: int):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        state = DiceGameState(self.creator, self.bet, self.mode, target)
        state.channel = interaction.channel
        _active_dice_games[self.creator.id] = state
        lobby_view = DiceLobbyView(state)
        lobby_embed = state.lobby_embed()
        await interaction.response.edit_message(embed=lobby_embed, view=lobby_view)
        state.lobby_msg = await interaction.original_response()

    @discord.ui.button(label="First to 1", style=discord.ButtonStyle.primary)
    async def t1_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._pick_target(interaction, 1)

    @discord.ui.button(label="First to 2", style=discord.ButtonStyle.primary)
    async def t2_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._pick_target(interaction, 2)

    @discord.ui.button(label="First to 3", style=discord.ButtonStyle.primary)
    async def t3_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._pick_target(interaction, 3)

    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary, emoji="✖️")
    async def cancel_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        async with get_user_lock(self.creator.id):
            conn = await get_conn()
            try:
                await update_balance(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)
        _end_game_session(self.creator.id)
        e = discord.Embed(
            title="🎲  Dice  ·  Cancelled",
            color=C_DARK,
            description="Game cancelled. Your bet has been returned to your balance."
        )
        _brand_embed(e)
        await interaction.response.edit_message(embed=e, view=None)

class DiceLobbyView(discord.ui.View):
    """Step 3 — public lobby with Join / Cancel buttons."""
    def __init__(self, state: DiceGameState):
        super().__init__(timeout=180)
        self.state    = state
        self._lock    = asyncio.Lock()
        self._joined  = False

    @discord.ui.button(label="Join", style=discord.ButtonStyle.green, emoji="🎲")
    async def join_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        state = self.state
        if interaction.user.id == state.creator.id:
            await interaction.response.send_message("❌ You can't join your own game.", ephemeral=True)
            return
        async with self._lock:
            if self._joined or state.opponent:
                await interaction.response.send_message("❌ Game already has an opponent.", ephemeral=True)
                return
            async with get_user_lock(interaction.user.id):
                conn = await get_conn()
                try:
                    await ensure_user(conn, interaction.user)
                    deducted = await deduct_balance_safe(conn, interaction.user.id, state.bet)
                    if not deducted:
                        row = await get_user(conn, interaction.user.id)
                        bal = row["balance"] if row else 0
                        await interaction.response.send_message(
                            f"❌ Need **{format_amount(state.bet)}** to join. You have **{format_amount(bal)}**.",
                            ephemeral=True)
                        return
                finally:
                    await release_conn(conn)
            if not _start_game_session(interaction.user.id):
                await interaction.response.send_message(
                    "⏳ You already have an active game running! Finish it before joining.", ephemeral=True)
                return
            state.opponent = interaction.user
            state.score[interaction.user.id] = 0
            state.waiting_roll = {state.creator.id, state.opponent.id}
            state.round_rolls  = {}
            state.round_num    = 1
            self._joined = True

        for item in self.children:
            item.disabled = True

        mode_label = "🔼 Normal  ·  Highest roll wins" if state.mode == "normal" else "🔽 Crazy  ·  Lowest roll wins"
        e = discord.Embed(
            title="🎲  Dice Battle  ·  Game Starting!",
            color=C_BLUE,
            description=(
                f"🔴 {state.creator.mention}  **vs**  🔵 {state.opponent.mention}\n\n"
                f"**Pot** » {format_amount(state.pot())}  ·  **Mode** » {mode_label}\n"
                f"**First to** » {state.target} round{'s' if state.target > 1 else ''} wins\n\n"
                f"⚔️  **Round 1** — both players use `/roll` to begin!"
            )
        )
        _brand_embed(e)
        await interaction.response.edit_message(embed=e, view=self)

    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary, emoji="✖️")
    async def cancel_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.state.creator.id:
            await interaction.response.send_message("❌ Only the creator can cancel.", ephemeral=True)
            return
        async with self._lock:
            if self._joined:
                await interaction.response.send_message("❌ Game already started.", ephemeral=True)
                return
        async with get_user_lock(self.state.creator.id):
            conn = await get_conn()
            try:
                await update_balance(conn, self.state.creator.id, self.state.bet)
            finally:
                await release_conn(conn)
        _active_dice_games.pop(self.state.creator.id, None)
        _end_game_session(self.state.creator.id)
        for item in self.children:
            item.disabled = True
        e = discord.Embed(
            title="🎲  Dice  ·  Cancelled",
            color=C_DARK,
            description="Game cancelled by the host. Your bet has been returned to your balance."
        )
        _brand_embed(e)
        await interaction.response.edit_message(embed=e, view=self)

    async def on_timeout(self):
        state = self.state
        if not self._joined:
            async with get_user_lock(state.creator.id):
                conn = await get_conn()
                try:
                    await update_balance(conn, state.creator.id, state.bet)
                finally:
                    await release_conn(conn)
            _active_dice_games.pop(state.creator.id, None)
            _end_game_session(state.creator.id)
            for item in self.children:
                item.disabled = True
            e = discord.Embed(
                title="🎲  Dice  ·  Lobby Expired",
                color=C_DARK,
                description="No opponent joined in time. Your bet has been returned to your balance."
            )
            _brand_embed(e)
            try:
                await state.lobby_msg.edit(embed=e, view=self)
            except Exception:
                pass

async def _process_dice_roll(state: DiceGameState, roller: discord.User,
                              channel: discord.abc.Messageable,
                              interaction: discord.Interaction = None):
    """Handle a /roll from one player. Sends roll result, resolves round if both rolled."""
    roll = random.randint(1, 6)
    state.round_rolls[roller.id] = roll
    state.waiting_roll.discard(roller.id)

    dice_emoji = DICE_EMOJIS[roll - 1] if roll - 1 < len(DICE_EMOJIS) else str(roll)
    roll_gif   = get_dice_gif(roll)

    roll_embed = discord.Embed(
        color=C_GOLD,
        description=f"{roller.mention} rolled a **{roll}**!"
    )
    if roll_gif:
        roll_embed.set_image(url=roll_gif)
    _brand_embed(roll_embed)

    if interaction is not None:
        await interaction.followup.send(content=roller.mention, embed=roll_embed)
    else:
        await channel.send(content=roller.mention, embed=roll_embed)

    if not state.waiting_roll and state.opponent and state.creator.id in state.round_rolls and state.opponent.id in state.round_rolls:
        await _resolve_dice_round(state, channel)

async def _resolve_dice_round(state: DiceGameState, channel: discord.abc.Messageable):
    """Resolve one round after both players have rolled."""
    creator_roll  = state.round_rolls[state.creator.id]
    opponent_roll = state.round_rolls[state.opponent.id]
    c_emoji = DICE_EMOJIS[creator_roll - 1] if creator_roll - 1 < len(DICE_EMOJIS) else str(creator_roll)
    o_emoji = DICE_EMOJIS[opponent_roll - 1] if opponent_roll - 1 < len(DICE_EMOJIS) else str(opponent_roll)

    if creator_roll == opponent_roll:
        tie_embed = discord.Embed(
            title="🤝  Tie  ·  Round Doesn't Count",
            color=C_PUSH,
            description=(
                f"🔴 {state.creator.mention} rolled {c_emoji} **{creator_roll}**\n"
                f"🔵 {state.opponent.mention} rolled {o_emoji} **{opponent_roll}**\n\n"
                f"Both rolled the same — it's a tie! Use `/roll` again to re-roll."
            )
        )
        _brand_embed(tie_embed)
        await channel.send(embed=tie_embed)
        state.waiting_roll = {state.creator.id, state.opponent.id}
        state.round_rolls  = {}
        return

    if state.mode == "normal":
        round_winner = state.creator if creator_roll > opponent_roll else state.opponent
    else:  # crazy — lowest wins
        round_winner = state.creator if creator_roll < opponent_roll else state.opponent
    round_loser  = state.opponent if round_winner.id == state.creator.id else state.creator

    state.score[round_winner.id] = state.score.get(round_winner.id, 0) + 1
    c_score = state.score.get(state.creator.id, 0)
    o_score = state.score.get(state.opponent.id, 0)
    score_line = f"**{state.creator.display_name}** {c_score}  —  {o_score} **{state.opponent.display_name}**"

    if state.score[round_winner.id] >= state.target:
        state.done = True
        pot     = state.pot()
        winner  = round_winner
        loser   = round_loser
        conn = await get_conn()
        try:
            payout = await apply_win_payout(conn, winner.id, pot, state.bet, "dice")
            profit = payout - state.bet
            await record_game(conn, winner.id, True,  state.bet, payout, "dice")
            await record_game(conn, loser.id,  False, state.bet, 0,      "dice")
            await log_transaction(conn, winner.id, "dice_win",  profit)
            await log_transaction(conn, loser.id,  "dice_loss", -state.bet)
            for uid in [winner.id, loser.id]:
                if channel.guild:
                    member = channel.guild.get_member(uid)
                    row    = await get_user(conn, uid)
                    if member and row:
                        await update_user_rank(member, row["wagered"])
        finally:
            await release_conn(conn)

        winner_avatar = await get_avatar(winner)
        win_embed = discord.Embed(
            title="🏆  Dice Battle  ·  We Have a Winner!",
            color=C_WIN,
            description=(
                f"🥇 **{winner.display_name}** wins the match!\n\n"
                f"**Final Score**\n"
                f"🔴 {state.creator.mention}  **{c_score}**  —  **{o_score}**  🔵 {state.opponent.mention}\n\n"
                f"**Bet** » {format_amount(state.bet)}  ·  **Payout** » {format_amount(payout)}"
            )
        )
        win_embed.set_thumbnail(url=winner_avatar)
        _brand_embed(win_embed)
        await channel.send(content=f"{winner.mention} {loser.mention}", embed=win_embed)

        log_e = discord.Embed(title="🎲  DICE RESULT", color=C_WIN)
        log_e.add_field(name="Winner",  value=winner.display_name,   inline=True)
        log_e.add_field(name="Loser",   value=loser.display_name,    inline=True)
        log_e.add_field(name="Payout",  value=format_amount(payout), inline=True)
        log_e.add_field(name="Mode",    value=state.mode.title(),    inline=True)
        log_e.set_footer(text=now_ts())
        await send_log(log_e)

        _active_dice_games.pop(state.creator.id, None)
        _end_game_session(state.creator.id)
        _end_game_session(state.opponent.id)

    else:
        state.round_num   += 1
        state.waiting_roll = {state.creator.id, state.opponent.id}
        state.round_rolls  = {}
        round_embed = discord.Embed(
            title=f"🎲  Round {state.round_num - 1} Result",
            color=C_WIN,
            description=(
                f"🔴 {state.creator.mention} rolled {c_emoji} **{creator_roll}**\n"
                f"🔵 {state.opponent.mention} rolled {o_emoji} **{opponent_roll}**\n\n"
                f"🏅 **{round_winner.display_name}** wins the round!\n"
                f"📊 Score » {score_line}\n\n"
                f"▶  **Round {state.round_num}** — use `/roll` to continue!"
            )
        )
        _brand_embed(round_embed)
        await channel.send(embed=round_embed)

@bot.tree.command(name="dice", description="Start a dice battle — Normal or Crazy mode, first to X wins!")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M")
async def cmd_dice(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("dice", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("dice", interaction.user):
        await interaction.response.send_message(
            "🔒 **Dice** is currently locked to staff only.", ephemeral=True)
        return
    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)

    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message(
            "⏳ You already have an active game running!", ephemeral=True)
        return

    mode_embed = discord.Embed(
        title="🎲  Dice Battle  ·  Pick a Mode",
        color=C_GOLD,
        description=(
            f"**Bet** » {format_amount(amt)}\n\n"
            f"🔼 **Normal** — Highest roll wins each round\n"
            f"🔽 **Crazy** — Lowest roll wins each round\n\n"
            f"Select a mode below to continue."
        )
    )
    _brand_embed(mode_embed)
    view = DiceModeView(interaction.user, amt, amt)
    await interaction.response.send_message(embed=mode_embed, view=view)

@bot.tree.command(name="roll", description="Roll the dice in your active dice game.")
async def cmd_roll(interaction: discord.Interaction):
    state = None
    creator_id = None
    for cid, s in list(_active_dice_games.items()):
        if interaction.user.id == s.creator.id or (s.opponent and interaction.user.id == s.opponent.id):
            state = s
            creator_id = cid
            break

    if not state:
        await interaction.response.send_message("❌ You're not in an active dice game.", ephemeral=True)
        return
    if state.done:
        await interaction.response.send_message("❌ Game is already over.", ephemeral=True)
        return
    if not state.opponent:
        await interaction.response.send_message("❌ Waiting for an opponent to join first.", ephemeral=True)
        return
    if interaction.user.id not in state.waiting_roll:
        await interaction.response.send_message("❌ You've already rolled this round — wait for your opponent.", ephemeral=True)
        return

    await interaction.response.defer()
    await _process_dice_roll(state, interaction.user, interaction.channel, interaction=interaction)

@bot.tree.command(name="coinflip", description="Flip a coin — heads or tails!")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M", side="Heads or Tails")
@app_commands.choices(side=[
    app_commands.Choice(name="Heads", value="Heads"),
    app_commands.Choice(name="Tails", value="Tails"),
])
async def cmd_coinflip(interaction: discord.Interaction, bet: str, side: str):
    wait = check_cooldown("coinflip", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("coinflip", interaction.user):
        await interaction.response.send_message(
            "🔒 **Coinflip** is currently locked to staff only.", ephemeral=True
        )
        return
    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)

    pf    = pf_new_game()
    pf["game_name"] = "Coinflip"
    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view  = CoinflipView(interaction.user, amt, side)
    view.creator_paid = True  # already deducted upfront
    view._pf_game_id  = pf["game_id"]
    embed = discord.Embed(
        color=C_GOLD,
        description=(
            f"## 🪙  COINFLIP\n"
            f"╔═══════════════════════╗\n"
            f"║  Wager  {format_amount(amt):>14}  ║\n"
            f"║  Side   {side:>14}  ║\n"
            f"╚═══════════════════════╝\n"
            f"Waiting for an opponent..."
        )
    )
    _brand_embed(embed)
    await interaction.response.send_message(embed=embed, view=view)
    view._original_message = await interaction.original_response()

ROULETTE_GIF_URLS = {
    "RED":    "https://cdn.discordapp.com/attachments/1497626978004500580/1500040552727707800/roulette_red.gif?ex=69f6fd21&is=69f5aba1&hm=89d59321c368f45d72b912a33b8c2e959e75543d4dd46463142bc49f5a1f6ac4&",
    "BLUE":   "https://cdn.discordapp.com/attachments/1497626978004500580/1500040249022218361/roulette_blue.gif?ex=69f6fcd8&is=69f5ab58&hm=8f582993bdca8e3e132031fd2ade3a22e6686f163321f673abb97c6fc4be29b3&",
    "YELLOW": "https://cdn.discordapp.com/attachments/1497626978004500580/1500040306513543188/roulette_yellow.gif?ex=69f6fce6&is=69f5ab66&hm=0e9bb071c4320bbce27f265507a5775326201d31548ebf07ee3662e3d9e050ad&",
}


class RouletteView(BaseGameView):
    def __init__(self, creator, bet):
        super().__init__(timeout=60)
        self.creator           = creator
        self.bet               = bet
        self.used              = False
        self._spin_lock        = asyncio.Lock()
        self._original_message = None

    async def _spin(self, interaction: discord.Interaction, chosen_emoji: str, chosen_name: str):
        async with self._spin_lock:
            if self.used:
                await interaction.response.send_message("❌ Already spinning!", ephemeral=True)
                return
            self.used = True

        await interaction.response.defer()
        msg = self._original_message

        # ── Decide result ─────────────────────────────────────────────────────
        _rlt_forced = _force_result.pop(self.creator.id, None)
        if _rlt_forced == "win":
            result_emoji, result_name, result_multi = next(
                (e, n, m) for e, n, p, m in ROULETTE_OUTCOMES if n == chosen_name
            )
        elif _rlt_forced == "lose":
            result_emoji, result_name, result_multi = next(
                (e, n, m) for e, n, p, m in ROULETTE_OUTCOMES if n != chosen_name
            )
        else:
            house_wins = random.random() < BOT_HOUSE_WIN
            if house_wins:
                losing_outcomes = [(e, n, m) for e, n, p, m in ROULETTE_OUTCOMES if n != chosen_name]
                result_emoji, result_name, result_multi = random.choice(losing_outcomes)
            else:
                result_emoji, result_name, result_multi = next(
                    (e, n, m) for e, n, p, m in ROULETTE_OUTCOMES if n == chosen_name
                )

        won    = chosen_name == result_name
        payout = min(int(self.bet * result_multi), MAX_PAYOUT) if won else 0
        color  = C_WIN if won else C_LOSS

        # ── Show spinning animation using the correct color GIF ───────────────
        gif_url = ROULETTE_GIF_URLS.get(result_name.upper(), "")
        gif_valid = bool(gif_url and gif_url.startswith("http"))

        spin_e = discord.Embed(
            color=C_GOLD,
            description=(
                f"## ◉  ROULETTE — ROLLING...\n"
                f"┌─────────────────────────┐\n"
                f"│ 💰 **Bet** • {format_amount(self.bet)} 💎\n"
                f"│ 🎯 **Pick** • {chosen_emoji} {chosen_name}\n"
                f"│ 🌀 **Spinning the wheel...**\n"
                f"└─────────────────────────┘"
            )
        )
        if gif_valid:
            spin_e.set_image(url=gif_url)
        _brand_embed(spin_e)
        try:
            await msg.edit(embed=spin_e, view=None)
        except Exception as e:
            print(f"[ROULETTE ANIM] {e}")

        await asyncio.sleep(3.5)

        # ── DB ────────────────────────────────────────────────────────────────
        try:
            conn = await get_conn()
            try:
                if won:
                    payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "roulette")
                await record_game(conn, self.creator.id, won, self.bet, payout, "roulette")
                await log_transaction(conn, self.creator.id, "roulette", payout - self.bet)
                if interaction.guild:
                    row = await get_user(conn, self.creator.id)
                    member = interaction.guild.get_member(self.creator.id)
                    if row and member:
                        await update_user_rank(member, row["wagered"])
            finally:
                await release_conn(conn)
        except Exception as _db_err:
            print(f"[ROULETTE DB ERROR] {_db_err}")

        # ── Result embed ──────────────────────────────────────────────────────
        profit_str   = f"+{format_amount(payout - self.bet)}" if won else f"-{format_amount(self.bet)}"
        outcome_line = "🏆 YOU WIN!" if won else "💀 YOU LOST!"
        result_color_icon = "🟢" if won else "🔴"

        result_e = discord.Embed(color=color)
        result_e.set_author(name=f"{self.creator.display_name}  ·  Roulette",
                            icon_url=self.creator.display_avatar.url)
        result_e.description = (
            f"## {result_color_icon} {outcome_line}\n"
            f"┌─────────────────────────┐\n"
            f"│ 💰 **Bet** • {format_amount(self.bet)} 💎\n"
            f"│ 🎯 **Pick** • {chosen_emoji} {chosen_name}\n"
            f"│ 🎡 **Landed** • {result_emoji} {result_name}\n"
            f"│ 📊 **Multi** • {result_multi}×\n"
            f"│ 💸 **Profit** • {profit_str} 💎\n"
            f"└─────────────────────────┘"
        )
        if gif_valid:
            result_e.set_image(url=gif_url)
        _brand_embed(result_e)

        try:
            await msg.edit(embed=result_e, view=None)
        except Exception as e:
            print(f"[ROULETTE RESULT] {e}")
        finally:
            self.stop()

        log_e = discord.Embed(title="◉  ROULETTE", color=color)
        log_e.add_field(name="Player", value=self.creator.mention,    inline=True)
        log_e.add_field(name="Bet",    value=format_amount(self.bet), inline=True)
        log_e.add_field(name="Chosen", value=f"{chosen_emoji} {chosen_name}", inline=True)
        log_e.add_field(name="Result", value=f"{result_emoji} {result_name}", inline=True)
        log_e.add_field(name="Won",    value="✅" if won else "❌",   inline=True)
        log_e.add_field(name="Payout", value=format_amount(payout),   inline=True)
        log_e.set_footer(text=now_ts())
        await send_log(log_e)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.used:
            conn = await get_conn()
            try:
                await update_balance(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)
            try:
                await self._original_message.edit(
                    embed=discord.Embed(color=C_DARK, description="## ◉  ROULETTE — EXPIRED\n> Timed out — bet refunded"),
                    view=None)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
        await super().on_timeout()

    @discord.ui.button(label="🔴 Red (2x)", style=discord.ButtonStyle.danger)
    async def red_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._spin(interaction, "🔴", "Red")

    @discord.ui.button(label="🔵 Blue (2x)", style=discord.ButtonStyle.primary)
    async def blue_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._spin(interaction, "🔵", "Blue")

    @discord.ui.button(label="🟡 Yellow (6x)", style=discord.ButtonStyle.secondary)
    async def yellow_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._spin(interaction, "🟡", "Yellow")

@bot.tree.command(name="roulette", description="Play roulette — Red/Blue (2x) or Yellow (6x).")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M")
async def cmd_roulette(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("roulette", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("roulette", interaction.user):
        await interaction.response.send_message(
            "🔒 **Roulette** is currently locked to staff only.", ephemeral=True
        )
        return
    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)

    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view  = RouletteView(interaction.user, amt)
    view.used = False  # will be set True on spin
    embed = discord.Embed(
        color=C_GOLD,
        description=(
            f"## ◉  ROULETTE\n"
            f"╔══════════════════════╗\n"
            f"║  Wager  {format_amount(amt):>14}  ║\n"
            f"╚══════════════════════╝\n"
            f"🔴 **Red** — 2×  ·  🔵 **Blue** — 2×  ·  🟡 **Yellow** — 6×\n"
            f"Pick your colour:"
        )
    )
    await interaction.response.send_message(embed=embed, view=view)
    view._original_message = await interaction.original_response()

SUITS = ["♠️", "♥️", "♦️", "♣️"]
RANKS = {1:"A", 2:"2", 3:"3", 4:"4", 5:"5", 6:"6", 7:"7",
         8:"8", 9:"9", 10:"10", 11:"J", 12:"Q", 13:"K"}

def bac_val(rank: int) -> int:
    return 0 if rank >= 10 else rank

def bac_total(hand) -> int:
    return sum(bac_val(c[0]) for c in hand) % 10

def bac_card() -> tuple:
    """Return a (rank, suit) tuple."""
    return (random.randint(1, 13), random.choice(SUITS))

def bac_str(hand) -> str:
    """Format hand like: A♣  2♣  A♣ = 4"""
    cards = "  ".join(f"{RANKS[r]}{s}" for r, s in hand)
    total = bac_total(hand)
    return f"{cards} = **{total}**"

def bac_str_hidden(hand) -> str:
    """Show only first card, rest hidden."""
    first = f"{RANKS[hand[0][0]]}{hand[0][1]}"
    return first + "  🂠" * (len(hand) - 1)

class BaccaratView(BaseGameView):
    def __init__(self, creator, bet):
        super().__init__(timeout=60)
        self.creator           = creator
        self.bet               = bet
        self.used              = False
        self._play_lock        = asyncio.Lock()
        self._original_message = None

    async def _play(self, interaction: discord.Interaction, bet_type: str):
        async with self._play_lock:
            if self.used:
                await interaction.response.send_message("❌ Already playing!", ephemeral=True)
                return
            self.used = True

        await interaction.response.defer()

        ph = [bac_card(), bac_card()]
        bh = [bac_card(), bac_card()]

        msg = self._original_message
        await msg.edit(embed=discord.Embed(
            title="🂡  BACCARAT",
            description="```\n  Shuffling...  🂠  🂠\n```",
            color=C_GOLD
        ), view=None)
        await asyncio.sleep(0.7)

        try:
            await msg.edit(embed=discord.Embed(
                title="🂡  BACCARAT",
                description=(
                    f"```\n"
                    f"  PLAYER     {RANKS[ph[0][0]]}{ph[0][1]}   🂠\n"
                    f"  BANKER     {RANKS[bh[0][0]]}{bh[0][1]}   🂠\n"
                    f"```"
                ),
                color=C_GOLD
            ))
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass
        await asyncio.sleep(0.7)

        try:
            await msg.edit(embed=discord.Embed(
                title="🂡  BACCARAT",
                description=(
                    f"```\n"
                    f"  PLAYER     {bac_str(ph)}\n"
                    f"  BANKER     {bac_str_hidden(bh)}\n"
                    f"```"
                ),
                color=C_GOLD
            ))
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass
        await asyncio.sleep(0.8)

        pt, bt  = bac_total(ph), bac_total(bh)
        natural = pt >= 8 or bt >= 8

        if not natural:
            drew_player = False
            if pt <= 5:
                ph.append(bac_card())
                pt = bac_total(ph)
                drew_player = True
                await msg.edit(embed=discord.Embed(
                    title="🂡  PLAYER DRAWS",
                    description=(
                        f"```\n"
                        f"  PLAYER  ◄  {bac_str(ph)}\n"
                        f"  BANKER     {bac_str_hidden(bh)}\n"
                        f"```"
                    ),
                    color=C_BLUE
                ))
                await asyncio.sleep(0.8)

            p3v = bac_val(ph[2][0]) if drew_player else None
            if p3v is None:
                if bt <= 5:
                    bh.append(bac_card())
            else:
                if bt <= 2:
                    bh.append(bac_card())
                elif bt == 3 and p3v != 8:
                    bh.append(bac_card())
                elif bt == 4 and p3v in range(2, 8):
                    bh.append(bac_card())
                elif bt == 5 and p3v in range(4, 8):
                    bh.append(bac_card())
                elif bt == 6 and p3v in [6, 7]:
                    bh.append(bac_card())

            if len(bh) == 3:
                bt = bac_total(bh)
                await msg.edit(embed=discord.Embed(
                    title="🂡  BANKER DRAWS",
                    description=(
                        f"```\n"
                        f"  PLAYER     {bac_str(ph)}\n"
                        f"  BANKER  ◄  {bac_str(bh)}\n"
                        f"```"
                    ),
                    color=C_BLUE
                ))
                await asyncio.sleep(0.8)

        bt = bac_total(bh)
        _bac_forced = _force_result.pop(self.creator.id, None)
        if _bac_forced == "win":
            player_bet_wins = True
        elif _bac_forced == "lose":
            player_bet_wins = False
        else:
            player_bet_wins = random.random() >= BOT_HOUSE_WIN  # 48% player wins

        if bet_type == "Tie":
            winner = "Player" if pt > bt else ("Banker" if bt > pt else "Tie")
        else:
            winner = bet_type if player_bet_wins else ("Banker" if bet_type == "Player" else "Player")

        if bet_type == winner:
            multiplier = 9.0 if winner == "Tie" else 2.0
            payout     = min(int(self.bet * multiplier), MAX_PAYOUT)
            won        = True
        elif winner == "Tie" and bet_type in ("Player", "Banker"):
            multiplier = 1.0
            payout     = self.bet   # push — stake returned
            won        = False
        else:
            multiplier = 0.0
            payout     = 0
            won        = False

        is_push = (winner == "Tie" and bet_type in ("Player", "Banker"))
        _bac_house_flip = random.random() < 0.03  # 3% extra house flip
        if won and not is_push and _bac_house_flip:
            won    = False
            payout = 0
        if not is_push:
            record_streak(self.creator.id, won)
        net     = payout - self.bet
        if won:
            title = "▲  WIN"
            color = C_WIN
        elif is_push:
            title = "⟳  PUSH"
            color = C_PUSH
        else:
            title = "▼  LOSS"
            color = C_LOSS

        if is_push:
            outcome_line = "🤝 It's a Tie!\n🤝 It's a tie!"
            outcome_icon = "Push 🤝"
            returned_val = format_amount(self.bet)
        elif won:
            outcome_line = f"**✦  YOU WIN  +{format_amount(payout - self.bet)}**"
            outcome_icon = "You Win! 🎉"
            returned_val = format_amount(payout)
        else:
            outcome_line = f"**✗  {winner.upper()} WINS**"
            outcome_icon = "You Lose 💀"
            returned_val = "0"

        bac_net_str = f"+{format_amount(payout - self.bet)} 💎" if payout > self.bet else ("±0" if payout == self.bet else f"-{format_amount(self.bet)}")
        def _bac_hand_display(hand):
            RANKS = {1:"A",2:"2",3:"3",4:"4",5:"5",6:"6",7:"7",8:"8",9:"9",10:"10",11:"J",12:"Q",13:"K"}
            SUITS = ["♠","♥","♦","♣"]
            parts = []
            for card in hand:
                if isinstance(card, tuple):
                    r, s = card
                else:
                    r, s = card, random.choice(SUITS)
                rank_str = RANKS.get(r % 13 or 13, str(r))
                parts.append(f"{rank_str}{s}")
            return " ".join(parts)
        p_display = bac_str(ph)
        b_display = bac_str(bh)
        if is_push:
            result_label = "It's a Tie!\n🤝 It's a tie!"
        elif won:
            result_label = f"**{bet_type} Wins!**\n🏆 {bet_type} wins this round!"
        else:
            result_label = f"**{winner} Wins!**\n🏦 {winner} wins this round!"

        result_embed = discord.Embed(
            color=color,
            description=(
                f"## 🎴  Baccarat Game\n"
                f"**Bet:** {format_amount(self.bet)} 💎\n"
                f"**On:** {bet_type}\n"
                f"**Result:** {bac_net_str}"
            )
        )
        result_embed.add_field(name="Player",  value=f"{p_display} = {pt}", inline=True)
        result_embed.add_field(name="Banker",  value=f"{b_display} = {bt}", inline=True)
        result_embed.add_field(name="​",  value="​",              inline=True)
        result_embed.add_field(name="​",  value=result_label,          inline=False)
        result_embed.set_thumbnail(url=await get_avatar(self.creator))
        _brand_embed(result_embed)

        try:
            conn = await get_conn()
            try:
                if payout > 0:
                    payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "baccarat")
                if not is_push:
                    await record_game(conn, self.creator.id, won, self.bet, payout)
                else:
                    await conn.execute(
                        "UPDATE users SET wagered=wagered+$1, last_updated=$2 WHERE user_id=$3",
                        self.bet, now_ts(), str(self.creator.id))
                await log_transaction(conn, self.creator.id, "baccarat", payout - self.bet)
                if interaction.guild:
                    row = await get_user(conn, self.creator.id)
                    member = interaction.guild.get_member(self.creator.id)
                    if row and member:
                        await update_user_rank(member, row["wagered"])
            finally:
                await release_conn(conn)
        except Exception as _db_err:
            print(f"[BACCARAT DB ERROR] {_db_err}")

        await asyncio.sleep(0.3)
        try:
            await msg.edit(embed=result_embed, view=None)
        except Exception as e:
            print(f'[RESULT DISPLAY FAILED] {e}')

        self.stop()
        log_e = discord.Embed(title="🎴 Baccarat Result", color=color)
        log_e.add_field(name="Player",   value=self.creator.mention,    inline=True)
        log_e.add_field(name="Bet On",   value=bet_type,                inline=True)
        log_e.add_field(name="Winner",   value=winner,                  inline=True)
        log_e.add_field(name="Wagered",  value=format_amount(self.bet), inline=True)
        log_e.add_field(name="Payout",   value=format_amount(payout),   inline=True)
        log_e.set_footer(text=now_ts())
        await send_log(log_e)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.used:
            conn = await get_conn()
            try:
                await update_balance(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)
            try:
                await self._original_message.edit(
                    embed=discord.Embed(title="🃏  Baccarat — Expired", description="⏰ Game timed out — bet refunded.", color=C_DARK),
                    view=None)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
        await super().on_timeout()

    @discord.ui.button(label="👤 Player (1:1)", style=discord.ButtonStyle.primary)
    async def player_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._play(interaction, "Player")

    @discord.ui.button(label="🏦 Banker (1:1)", style=discord.ButtonStyle.secondary)
    async def banker_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._play(interaction, "Banker")

    @discord.ui.button(label="🤝 Tie (8:1)", style=discord.ButtonStyle.success)
    async def tie_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._play(interaction, "Tie")

@bot.tree.command(name="baccarat", description="Play baccarat — Player, Banker, or Tie.")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M")
async def cmd_baccarat(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("baccarat", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("baccarat", interaction.user):
        await interaction.response.send_message(
            "🔒 **Baccarat** is currently locked to staff only.", ephemeral=True
        )
        return
    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)

    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view  = BaccaratView(interaction.user, amt)
    embed = discord.Embed(
        color=C_GOLD,
        description=(
            f"## 🎴  BACCARAT\n"
            f"╔══════════════════════╗\n"
            f"║  Wager  {format_amount(amt):>14}  ║\n"
            f"╚══════════════════════╝\n"
            f"👤 **Player** 1:1  ·  🏦 **Banker** 1:1  ·  🤝 **Tie** 8:1\n"
            f"Pick your side — closest to **9** wins:"
        )
    )
    _brand_embed(embed)
    await interaction.response.send_message(embed=embed, view=view)
    view._original_message = await interaction.original_response()

def build_deck():
    deck = list(range(1, 14)) * 4
    random.shuffle(deck)
    return deck

def bj_val(rank: int) -> int:
    return 10 if rank > 10 else rank

def bj_total(hand) -> int:
    total = sum(bj_val(c) for c in hand)
    aces  = hand.count(1)
    while aces > 0 and total + 10 <= 21:
        total += 10
        aces  -= 1
    return total

def bj_str(hand, hide_second=False) -> str:
    if hide_second and len(hand) >= 2:
        return f"{CARD_EMOJIS[hand[0]]} 🂠"
    return " ".join(CARD_EMOJIS[c] for c in hand)

def is_blackjack(hand) -> bool:
    return len(hand) == 2 and bj_total(hand) == 21

class BlackjackView(BaseGameView):
    def __init__(self, creator, bet, deck, player_hand, dealer_hand):
        super().__init__(timeout=120)
        self.creator            = creator
        self.bet                = bet
        self.deck               = deck
        self.player_hand        = player_hand
        self.dealer_hand        = dealer_hand
        self.done               = False
        self.extra_bet          = 0    # tracks double-down extra bet
        self._bet_deducted      = False  # guard so we only deduct the initial bet once
        self._original_message  = None

    def game_embed(self, hide_dealer=True) -> discord.Embed:
        pt          = bj_total(self.player_hand)
        dt          = bj_total([self.dealer_hand[0]]) if hide_dealer else bj_total(self.dealer_hand)
        dlabel      = "?" if hide_dealer else str(bj_total(self.dealer_hand))
        total_bet   = self.bet + self.extra_bet
        player_bj   = is_blackjack(self.player_hand) and self.extra_bet == 0
        potential   = int(total_bet * 2.5) if player_bj else total_bet * 2

        player_cards = bj_str(self.player_hand)
        dealer_cards = bj_str(self.dealer_hand, hide_dealer)

        embed = discord.Embed(
            color=C_GOLD,
            description=(
                f"## ♠️  BLACKJACK\n"
                f"╔══════════════════════╗\n"
                f"║  Wager  {format_amount(total_bet):>14}  ║\n"
                f"║  Max    {format_amount(potential):>14}  ║\n"
                f"╚══════════════════════╝"
            )
        )
        embed.add_field(
            name="Your Hand:",
            value=f"{player_cards}\nPlayer's Card Value: {pt}",
            inline=False
        )
        embed.add_field(
            name="Dealer's Hand:",
            value=f"{dealer_cards}\nDealer's Card Value: {dlabel}",
            inline=False
        )
        _brand_embed(embed)
        return embed

    async def _deduct_initial_bet(self) -> bool:
        """Deduct the initial bet exactly once. Returns True if successful."""
        if self._bet_deducted:
            return True
        self._bet_deducted = True
        async with get_user_lock(self.creator.id):
            conn = await get_conn()
            try:
                return await deduct_balance_safe(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)

    async def _end_game(self, interaction: discord.Interaction):
        """Resolve the game. Caller must have already deferred the interaction."""
        deducted = await self._deduct_initial_bet()
        if not deducted:
            try:
                await self._original_message.edit(content="❌ Insufficient balance. Game cancelled.", embed=None, view=None)
            except Exception as e:
                print(f'[BJ END GAME FAILED] {e}')
            self.done = True
            self.stop()
            return

        self.done = True
        self.stop()

        while bj_total(self.dealer_hand) < BJ_DEALER_STAND:
            self.dealer_hand.append(self.deck.pop())
            await asyncio.sleep(0.5)
            try:
                await self._original_message.edit(embed=self.game_embed(hide_dealer=False))
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass

        total_bet = self.bet + self.extra_bet
        pt        = bj_total(self.player_hand)
        dt        = bj_total(self.dealer_hand)
        player_bj = is_blackjack(self.player_hand) and self.extra_bet == 0
        dealer_bj = is_blackjack(self.dealer_hand)

        if pt > 21:
            result, payout, color = "BUST", 0, C_LOSS
        elif dt > 21:
            result, payout, color = "DEALER BUST", total_bet * 2, C_WIN
        elif player_bj and not dealer_bj:
            payout = min(int(total_bet * 2.5), MAX_PAYOUT)
            result, color = "BLACKJACK", C_WIN
        elif dealer_bj and not player_bj:
            result, payout, color = "DEALER BLACKJACK", 0, C_LOSS
        elif pt > dt:
            result, payout, color = f"{pt} VS {dt}", total_bet * 2, C_WIN
        elif dt > pt:
            result, payout, color = f"{dt} VS {pt}", 0, C_LOSS
        else:
            result, payout, color = f"PUSH  {pt} VS {dt}", total_bet, C_PUSH

        is_push = (payout == total_bet and pt == dt)
        won     = payout > total_bet

        net = payout - total_bet
        net_str = f"+{format_amount(net)}" if net > 0 else (f"-{format_amount(abs(net))}" if net < 0 else "±0")
        win_icon  = "🏆" if won else ("🔁" if is_push else "💀")
        win_title = "YOU WIN" if won else ("PUSH" if is_push else "YOU LOSE")
        embed = discord.Embed(
            color=color,
            title=f"🃏  Blackjack — {result}",
            description=(
                f"# {win_icon}  {win_title}  {win_icon}\n\n"
                f"**Bet:** {format_amount(total_bet)} 💎"
            )
        )
        embed.add_field(
            name="Your Hand:",
            value=f"{bj_str(self.player_hand)}\nPlayer's Card Value: **{pt}**",
            inline=False
        )
        embed.add_field(
            name="Dealer's Hand:",
            value=f"{bj_str(self.dealer_hand)}\nDealer's Card Value: **{dt}**",
            inline=False
        )
        net_str2 = f"+{format_amount(payout - total_bet)}" if won else (f"-{format_amount(total_bet)}" if not is_push else "±0")
        embed.add_field(name="Result", value=f"`{net_str2}` 💎", inline=True)
        embed.add_field(name="Payout", value=f"`{format_amount(payout)}` 💎", inline=True)
        _brand_embed(embed)

        try:
            conn = await get_conn()
            try:
                if payout > 0:
                    payout = await apply_win_payout(conn, self.creator.id, payout, total_bet, "blackjack")
                if not is_push:
                    await record_game(conn, self.creator.id, won, total_bet, payout)
                    await log_transaction(conn, self.creator.id, "blackjack", payout - total_bet)
                    _rank_guild = interaction.guild or bot.get_guild(GUILD_ID)
                    if _rank_guild:
                        row = await get_user(conn, self.creator.id)
                        member = _rank_guild.get_member(self.creator.id)
                        if row and member:
                            await update_user_rank(member, row["wagered"])
                else:
                    await log_transaction(conn, self.creator.id, "blackjack_push", 0)
            finally:
                await release_conn(conn)
        except Exception as e:
            print(f"[BJ DB ERROR] {e}")

        try:
            await self._original_message.edit(embed=embed, view=None)
        except Exception as e:
            print(f'[BJ RESULT FAILED] {e}')

        log_e = discord.Embed(title="♠️ Blackjack Result", color=color)
        log_e.add_field(name="Player",  value=self.creator.mention,        inline=True)
        log_e.add_field(name="Bet",     value=format_amount(total_bet),    inline=True)
        log_e.add_field(name="Payout",  value=format_amount(payout),       inline=True)
        log_e.add_field(name="Outcome", value="PUSH" if is_push else ("✅ WIN" if won else "❌ LOSS"), inline=True)
        log_e.set_footer(text=now_ts())
        await send_log(log_e)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.done:
            refund = self.bet + self.extra_bet
            conn = await get_conn()
            try:
                await update_balance(conn, self.creator.id, refund)
            finally:
                await release_conn(conn)
            try:
                await self._original_message.edit(
                    embed=discord.Embed(
                        title="♠️ Blackjack — Timed Out",
                        description=f"Game expired due to inactivity. **{format_amount(refund)}** refunded.",
                        color=C_DARK),
                    view=None)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
        await super().on_timeout()
        await super().on_timeout()
    @discord.ui.button(label="Hit", style=discord.ButtonStyle.blurple, emoji="🃏")
    async def hit_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id or self.done:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await interaction.response.defer()
        deducted = await self._deduct_initial_bet()
        if not deducted:
            try:
                await interaction.edit_original_response(content="❌ Insufficient balance. Game cancelled.", embed=None, view=None)
            except Exception as e:
                print(f'[BJ HIT FAILED] {e}')
            self.done = True
            self.stop()
            return
        self.player_hand.append(self.deck.pop())
        if bj_total(self.player_hand) >= 21:
            try:
                await interaction.edit_original_response(embed=self.game_embed(hide_dealer=True), view=self)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
            await asyncio.sleep(0.4)
            await self._end_game(interaction)
        else:
            try:
                await interaction.edit_original_response(embed=self.game_embed(hide_dealer=True), view=self)
            except Exception as e:
                print(f'[BJ HIT UPDATE FAILED] {e}')

    @discord.ui.button(label="Stand", style=discord.ButtonStyle.danger, emoji="✋")
    async def stand_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id or self.done:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await interaction.response.defer()
        await self._end_game(interaction)

    @discord.ui.button(label="Double", style=discord.ButtonStyle.blurple, emoji="✖️")
    async def double_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id or self.done:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        if len(self.player_hand) != 2:
            await interaction.response.send_message("❌ Can only double on first 2 cards.", ephemeral=True)
            return

        await interaction.response.defer()

        deducted_initial = await self._deduct_initial_bet()
        if not deducted_initial:
            try:
                await interaction.edit_original_response(content="❌ Insufficient balance. Game cancelled.", embed=None, view=None)
            except Exception as e:
                print(f'[BJ DOUBLE FAILED] {e}')
            self.done = True
            self.stop()
            return

        async with get_user_lock(self.creator.id):
            conn = await get_conn()
            try:
                deducted_extra = await deduct_balance_safe(conn, self.creator.id, self.bet)
                if not deducted_extra:
                    row = await get_user(conn, self.creator.id)
                    bal = row["balance"] if row else 0
                    try:
                        await interaction.edit_original_response(
                            content=f"❌ Need **{format_amount(self.bet)}** more to double. You have **{format_amount(bal)}**. Try Hit or Stand instead.",
                            embed=self.game_embed(hide_dealer=True), view=self)
                    except Exception as e:
                        print(f'[BJ DOUBLE EXTRA FAILED] {e}')
                    return
            finally:
                await release_conn(conn)

        self.extra_bet = self.bet
        self.player_hand.append(self.deck.pop())
        await self._end_game(interaction)

@bot.tree.command(name="blackjack", description="Play blackjack against the dealer.")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M")
async def cmd_blackjack(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("blackjack", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("blackjack", interaction.user):
        await interaction.response.send_message(
            "🔒 **Blackjack** is currently locked to staff only.", ephemeral=True
        )
        return
    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)

    deck = build_deck()
    ph   = [deck.pop(), deck.pop()]
    dh   = [deck.pop(), deck.pop()]
    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view = BlackjackView(interaction.user, amt, deck, ph, dh)
    view._bet_deducted = True  # already deducted upfront

    embed = view.game_embed(hide_dealer=True)
    embed.set_footer(text="Hit • Stand • Double (first 2 cards only)")
    await interaction.response.send_message(embed=embed, view=view)
    view._original_message = await interaction.original_response()

    if is_blackjack(ph):
        await asyncio.sleep(1)
        view.done = True
        view.stop()

        msg = view._original_message
        deducted = await view._deduct_initial_bet()
        if not deducted:
            try:
                await msg.edit(content="❌ Insufficient balance. Game cancelled.", embed=None, view=None)
            except Exception as e:
                print(f'[BJ INSTANT INSUF FAILED] {e}')
            return

        while bj_total(dh) < 17:
            dh.append(deck.pop())

        dealer_bj = is_blackjack(dh)
        total_bet  = amt
        pt         = bj_total(ph)
        dt         = bj_total(dh)

        if dealer_bj:
            result, payout, color = "Push — Both Blackjack! Bet returned.", amt, C_PUSH
            is_push = True
            won     = False
        else:
            payout  = int(amt * 2.5)
            result  = f"BLACKJACK! You win {format_amount(payout)} 💎! 🎉"
            color   = C_WIN
            is_push = False
            won     = True

        _net_bj = payout - total_bet
        _net_str_bj = f"+{format_amount(_net_bj)}" if _net_bj > 0 else (f"-{format_amount(abs(_net_bj))}" if _net_bj < 0 else "±0")
        bj_embed = discord.Embed(color=color, description=f"## ♠️  BJ — {result}")
        bj_embed.add_field(name=f"🃏 Your Hand ({pt})",   value=f"`{bj_str(ph)}`", inline=False)
        bj_embed.add_field(name=f"🎴 Dealer Hand ({dt})", value=f"`{bj_str(dh)}`", inline=False)
        bj_embed.add_field(name="💰 Bet",    value=f"**{format_amount(total_bet)} 💎**", inline=True)
        bj_embed.add_field(name="🎁 Payout", value=f"**{format_amount(payout)} 💎**",   inline=True)
        bj_embed.add_field(name="📈 Net",    value=f"**{_net_str_bj}**",             inline=True)
        bj_embed.set_thumbnail(url=await get_avatar(interaction.user))

        conn = await get_conn()
        try:
            if payout > 0:
                payout = await apply_win_payout(conn, interaction.user.id, payout, total_bet, "blackjack")
            if not is_push:
                await record_game(conn, interaction.user.id, won, total_bet, payout)
                await log_transaction(conn, interaction.user.id, "blackjack", payout - total_bet)
                if won and interaction.guild:
                    row = await get_user(conn, interaction.user.id)
                    member = interaction.guild.get_member(interaction.user.id)
                    if row and member:
                        await update_user_rank(member, row["wagered"])
            else:
                await log_transaction(conn, interaction.user.id, "blackjack_push", 0)
        finally:
            await release_conn(conn)

        try:
            await msg.edit(embed=bj_embed, view=None)
        except Exception as e:
            print(f'[BJ INSTANT RESULT FAILED] {e}')

BJD_DICE_FACES = ["1️⃣","2️⃣","3️⃣","4️⃣","5️⃣","6️⃣"]

def bjd_roll() -> int:
    return random.randint(1, 6)

def bjd_total(dice: list) -> int:
    return sum(dice)

def bjd_str(dice: list, hide_last: bool = False) -> str:
    if hide_last and len(dice) > 1:
        shown = " ".join(BJD_DICE_FACES[d-1] for d in dice[:-1])
        return f"{shown} ❓"
    return " ".join(BJD_DICE_FACES[d-1] for d in dice)

def bjd_is_blackjack(dice: list) -> bool:
    return len(dice) == 2 and bjd_total(dice) == 21

class BlackjackDiceView(BaseGameView):
    def __init__(self, creator, bet, player_dice, dealer_dice):
        super().__init__(timeout=120)
        self.creator         = creator
        self.bet             = bet
        self.player_dice     = player_dice
        self.dealer_dice     = dealer_dice
        self.done            = False
        self.extra_bet       = 0
        self._bet_deducted   = False
        self._original_message = None

    def game_embed(self, hide_dealer=True) -> discord.Embed:
        pt        = bjd_total(self.player_dice)
        dt_shown  = self.dealer_dice[0] if hide_dealer else bjd_total(self.dealer_dice)
        dlabel    = f"{dt_shown}?" if hide_dealer else str(bjd_total(self.dealer_dice))
        total_bet = self.bet + self.extra_bet
        player_bj = bjd_is_blackjack(self.player_dice) and self.extra_bet == 0
        potential = int(total_bet * 2.5) if player_bj else total_bet * 2
        embed = discord.Embed(color=C_GOLD, description="## ⬛  BLACKJACK DICE")
        embed.add_field(name=f"Your Dice ({pt})",    value=bjd_str(self.player_dice),              inline=False)
        embed.add_field(name=f"Dealer Dice ({dlabel})", value=bjd_str(self.dealer_dice, hide_dealer), inline=False)
        embed.add_field(name="Bet",                  value=f"{format_amount(total_bet)} 💎",       inline=True)
        embed.add_field(name="Potential Payout",     value=f"{format_amount(potential)} 💎",       inline=True)
        return embed

    async def _deduct_initial_bet(self) -> bool:
        if self._bet_deducted:
            return True
        self._bet_deducted = True
        async with get_user_lock(self.creator.id):
            conn = await get_conn()
            try:
                return await deduct_balance_safe(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)

    async def _end_game(self, interaction: discord.Interaction):
        deducted = await self._deduct_initial_bet()
        if not deducted:
            try:
                await self._original_message.edit(content="❌ Insufficient balance. Game cancelled.", embed=None, view=None)
            except Exception as e:
                print(f'[BJ END GAME FAILED] {e}')
            self.done = True
            self.stop()
            return

        self.done = True
        self.stop()

        while bjd_total(self.dealer_dice) < 17:
            self.dealer_dice.append(bjd_roll())
            await asyncio.sleep(0.4)
            try:
                await self._original_message.edit(embed=self.game_embed(hide_dealer=False))
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass

        total_bet = self.bet + self.extra_bet
        pt = bjd_total(self.player_dice)
        dt = bjd_total(self.dealer_dice)
        player_bj = bjd_is_blackjack(self.player_dice) and self.extra_bet == 0

        if pt > 21:
            result, payout, color = f"Bust! {pt}", 0, C_LOSS
        elif player_bj and dt != 21:
            result, payout, color = f"Blackjack! 🎉", int(total_bet * 2.5), C_WIN
        elif dt > 21:
            result, payout, color = f"Dealer Busts! 🎉", total_bet * 2, C_WIN
        elif pt > dt:
            result, payout, color = f"You Win! {pt} vs {dt}", total_bet * 2, C_WIN
        elif dt > pt:
            result, payout, color = f"Dealer Wins! {dt} vs {pt}", 0, C_LOSS
        else:
            result, payout, color = f"Push! {pt} vs {dt}", total_bet, C_PUSH

        is_push = (payout == total_bet and pt == dt)
        won     = payout > total_bet

        bj_embed = discord.Embed(
            color=color,
            description=(
                f"## ⬛  BJ DICE — {result}\n"
                f"```\n"
                f"  You    {bjd_str(self.player_dice):>20}  ({pt})\n"
                f"  Dealer {bjd_str(self.dealer_dice):>20}  ({dt})\n"
                f"```\n"
                f"{result_desc(won, is_push, total_bet, payout)}"
            )
        )
        bj_embed.set_thumbnail(url=await get_avatar(self.creator))

        try:
            conn = await get_conn()
            try:
                if payout > 0:
                    payout = await apply_win_payout(conn, self.creator.id, payout, total_bet, "blackjack_dice")
                if not is_push:
                    await record_game(conn, self.creator.id, won, total_bet, payout)
                    await log_transaction(conn, self.creator.id, "bjdice", payout - total_bet)
                    _rank_guild = interaction.guild or bot.get_guild(GUILD_ID)
                    if _rank_guild:
                        row = await get_user(conn, self.creator.id)
                        member = _rank_guild.get_member(self.creator.id)
                        if row and member:
                            await update_user_rank(member, row["wagered"])
                else:
                    await log_transaction(conn, self.creator.id, "bjdice_push", 0)
            finally:
                await release_conn(conn)
        except Exception as _db_err:
            print(f"[BJDICE DB ERROR] {_db_err}")

        try:
            await msg.edit(embed=bj_embed, view=None)
        except Exception as e:
            print(f'[BJ INSTANT RESULT FAILED] {e}')

        log_e = discord.Embed(title="🎲 Blackjack Dice Result", color=color)
        log_e.add_field(name="Player",  value=self.creator.mention,        inline=True)
        log_e.add_field(name="Bet",     value=format_amount(total_bet),    inline=True)
        log_e.add_field(name="Payout",  value=format_amount(payout),       inline=True)
        log_e.add_field(name="Outcome", value="PUSH" if is_push else ("✅ WIN" if won else "❌ LOSS"), inline=True)
        log_e.set_footer(text=now_ts())
        await send_log(log_e)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.done:
            refund = self.bet + self.extra_bet
            conn = await get_conn()
            try:
                await update_balance(conn, self.creator.id, refund)
            finally:
                await release_conn(conn)
            try:
                await self._original_message.edit(
                    embed=discord.Embed(color=C_DARK, title=None, description="## ⬛  BJ DICE — EXPIRED"),
                    view=None)
            except Exception as e:
                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
        await super().on_timeout()
    @discord.ui.button(label="Hit", style=discord.ButtonStyle.primary, emoji="🎲")
    async def hit_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id or self.done:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await interaction.response.defer()
        deducted = await self._deduct_initial_bet()
        if not deducted:
            try:
                await interaction.edit_original_response(content="❌ Insufficient balance. Game cancelled.", embed=None, view=None)
            except Exception as e:
                print(f'[BJDICE HIT FAILED] {e}')
            self.done = True
            self.stop()
            return
        self.player_dice.append(bjd_roll())
        if bjd_total(self.player_dice) >= 21:
            try:
                await interaction.edit_original_response(embed=self.game_embed(hide_dealer=True), view=self)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
            await asyncio.sleep(0.4)
            await self._end_game(interaction)
        else:
            try:
                await interaction.edit_original_response(embed=self.game_embed(hide_dealer=True), view=self)
            except Exception as e:
                print(f'[BJDICE HIT UPDATE FAILED] {e}')

    @discord.ui.button(label="Stand", style=discord.ButtonStyle.danger, emoji="✋")
    async def stand_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id or self.done:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await interaction.response.defer()
        await self._end_game(interaction)

    @discord.ui.button(label="Double", style=discord.ButtonStyle.blurple, emoji="✖️")
    async def double_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id or self.done:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        if len(self.player_dice) != 2:
            await interaction.response.send_message("❌ Can only double on first 2 dice.", ephemeral=True)
            return
        await interaction.response.defer()
        deducted = await self._deduct_initial_bet()
        if not deducted:
            try:
                await interaction.edit_original_response(content="❌ Insufficient balance. Game cancelled.", embed=None, view=None)
            except Exception as e:
                print(f'[BJDICE DOUBLE FAILED] {e}')
            self.done = True
            self.stop()
            return
        async with get_user_lock(self.creator.id):
            conn = await get_conn()
            try:
                ok = await deduct_balance_safe(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)
        if not ok:
            try:
                await interaction.edit_original_response(content="❌ Need more balance to double. Try Hit or Stand.", embed=self.game_embed(hide_dealer=True), view=self)
            except Exception as e:
                print(f'[BJDICE DOUBLE EXTRA FAILED] {e}')
            return
        self.extra_bet = self.bet
        self.player_dice.append(bjd_roll())
        await self._end_game(interaction)

@bot.tree.command(name="blackjackdice", description="Play Blackjack with dice — roll to 21!")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M")
async def cmd_blackjackdice(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("blackjackdice", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(
            f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("blackjackdice", interaction.user):
        await interaction.response.send_message(
            "🔒 **Blackjackdice** is currently locked to staff only.", ephemeral=True
        )
        return
    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return
    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)

    player_dice = [bjd_roll(), bjd_roll()]
    dealer_dice = [bjd_roll(), bjd_roll()]
    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view = BlackjackDiceView(interaction.user, amt, player_dice, dealer_dice)
    view._bet_deducted = True  # already deducted upfront
    await interaction.response.send_message(embed=view.game_embed(), view=view)
    view._original_message = await interaction.original_response()

WAR_SUITS = ["♠️", "♥️", "♦️", "♣️"]
WAR_RANKS = {2:"2",3:"3",4:"4",5:"5",6:"6",7:"7",
             8:"8",9:"9",10:"10",11:"J",12:"Q",13:"K",14:"A"}

def war_card() -> tuple:
    return (random.randint(2, 14), random.choice(WAR_SUITS))

def war_card_str(card: tuple) -> str:
    rank, suit = card
    return f"`{WAR_RANKS[rank]}{suit}`"

class WarView(BaseGameView):
    def __init__(self, creator: discord.User, bet: int):
        super().__init__(timeout=120)
        self.creator           = creator
        self.bet               = bet
        self.opponent          = None
        self.vs_bot            = False
        self.started           = False
        self._join_lock        = asyncio.Lock()
        self._original_message = None

    @discord.ui.button(label="Join", style=discord.ButtonStyle.green, emoji="🤝")
    async def join_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id == self.creator.id:
            await interaction.response.send_message("❌ Can't join your own game.", ephemeral=True)
            return
        async with self._join_lock:
            if self.opponent or self.vs_bot:
                await interaction.response.send_message("❌ Game already has an opponent.", ephemeral=True)
                return

        await interaction.response.defer()

        async with self._join_lock:
            async with get_user_lock(interaction.user.id):
                conn = await get_conn()
                try:
                    await ensure_user(conn, interaction.user)
                    deducted = await deduct_balance_safe(conn, interaction.user.id, self.bet)
                    if not deducted:
                        row = await get_user(conn, interaction.user.id)
                        bal = row["balance"] if row else 0
                        await interaction.followup.send(
                            f"❌ Need **{format_amount(self.bet)}** to join. You have **{format_amount(bal)}**.",
                            ephemeral=True)
                        return
                    self.opponent = interaction.user
                finally:
                    await release_conn(conn)
        await interaction.followup.send(
            f"✅ {interaction.user.mention} joined! Creator press **Start**.")

    @discord.ui.button(label="vs Bot", style=discord.ButtonStyle.blurple, emoji="🤖")
    async def bot_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Only the creator can do this.", ephemeral=True)
            return
        async with self._join_lock:
            if self.opponent or self.vs_bot:
                await interaction.response.send_message("❌ Already has an opponent.", ephemeral=True)
                return
            self.vs_bot = True
        await interaction.response.defer()
        try:
            await interaction.edit_original_response(
                embed=discord.Embed(
                    title="⚔️ WAR",
                    description=f"💰 **Bet** • {format_amount(self.bet)} 💎\
\
🤖 Bot called! Press **Start** to draw cards.",
                    color=C_LOSS),
                view=self)
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass

    @discord.ui.button(label="Start", style=discord.ButtonStyle.red, emoji="▶")
    async def start_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Only the creator can start.", ephemeral=True)
            return
        if not self.opponent and not self.vs_bot:
            await interaction.response.send_message("❌ Need an opponent first.", ephemeral=True)
            return
        if self.started:
            return

        await interaction.response.defer()
        self.started = True
        await self._resolve(interaction)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.started:
            try:
                await self._original_message.edit(
                    embed=discord.Embed(color=C_DARK, description="## ⚔️  WAR — EXPIRED\n> Timed out — bet refunded"),
                    view=None)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
            conn = await get_conn()
            try:
                await update_balance(conn, self.creator.id, self.bet)
                if self.opponent:
                    await update_balance(conn, self.opponent.id, self.bet)
            finally:
                await release_conn(conn)
        await super().on_timeout()

    async def _resolve(self, interaction: discord.Interaction):
        if not interaction.response.is_done():
            msg = self._original_message
        try:
            await msg.edit(embed=discord.Embed(color=C_GOLD, description="## ⚔️  WAR\n> Drawing cards..."), view=None)
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass
        for sym in ["♠️", "♥️", "♦️", "♣️", "♠️"]:
            try:
                await msg.edit(embed=discord.Embed(
                    title="⚔️ WAR", description=f"Drawing cards... {sym}", color=C_LOSS))
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
            await asyncio.sleep(0.35)

        creator_card  = war_card()
        opponent_card = war_card()
        opponent_label = "🤖 Bot" if self.vs_bot else self.opponent.mention
        opponent_name  = "🤖 Bot" if self.vs_bot else self.opponent.display_name

        if self.vs_bot:
            bot_wins = random.random() < get_dynamic_house_win(self.creator.id)
            for _ in range(50):
                creator_card  = war_card()
                opponent_card = war_card()
                if creator_card[0] == opponent_card[0]:
                    continue
                if bot_wins     and opponent_card[0] > creator_card[0]: break
                if not bot_wins and creator_card[0]  > opponent_card[0]: break

        creator_rank  = creator_card[0]
        opponent_rank = opponent_card[0]
        is_tie        = creator_rank == opponent_rank
        creator_won   = creator_rank > opponent_rank

        try:
            conn = await get_conn()
            try:
                if is_tie:
                    await conn.execute(
                        "UPDATE users SET wagered=wagered+$1, last_updated=$2 WHERE user_id=$3",
                        self.bet, now_ts(), str(self.creator.id))
                    await log_transaction(conn, self.creator.id, "war_tie", 0)
                    if not self.vs_bot:
                        await conn.execute(
                            "UPDATE users SET wagered=wagered+$1, last_updated=$2 WHERE user_id=$3",
                            self.bet, now_ts(), str(self.opponent.id))
                        await log_transaction(conn, self.opponent.id, "war_tie", 0)
                    await update_balance(conn, self.creator.id, self.bet)
                    if not self.vs_bot and self.opponent:
                        await update_balance(conn, self.opponent.id, self.bet)
                    color        = C_PUSH
                    title        = "↩️ WAR — TIE!"
                    payout       = self.bet
                    result_line  = "It's a tie! Both bets returned."
                    outcome_str  = "TIE"
                elif creator_won:
                    payout = min(self.bet * 2, MAX_PAYOUT)
                    payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "war")
                    await record_game(conn, self.creator.id, True,  self.bet, payout)
                    await log_transaction(conn, self.creator.id, "war_win", self.bet)
                    if not self.vs_bot:
                        await record_game(conn, self.opponent.id, False, self.bet, 0)
                        await log_transaction(conn, self.opponent.id, "war_loss", -self.bet)
                    color       = C_WIN
                    title       = "💰 WAR — YOU WIN!"
                    result_line = f"{self.creator.mention} wins!"
                    outcome_str = "WIN"
                else:
                    payout = 0
                    await record_game(conn, self.creator.id, False, self.bet, 0, "war")
                    await log_transaction(conn, self.creator.id, "war_loss", -self.bet)
                    if not self.vs_bot:
                        opp_payout = min(self.bet * 2, MAX_PAYOUT)
                        opp_payout = await apply_win_payout(conn, self.opponent.id, opp_payout, self.bet, "war")
                        await record_game(conn, self.opponent.id, True, self.bet, opp_payout)
                        await log_transaction(conn, self.opponent.id, "war_win", self.bet)
                    color       = C_LOSS
                    title       = "💸 WAR — YOU LOST!"
                    result_line = f"{opponent_label} wins!"
                    outcome_str = "LOSS"

                if interaction.guild:
                    for uid in ([self.creator.id] + ([] if self.vs_bot else [self.opponent.id])):
                        row = await get_user(conn, uid)
                        member = interaction.guild.get_member(uid)
                        if row and member:
                            await update_user_rank(member, row["wagered"])
            finally:
                await release_conn(conn)
        except Exception as _db_err:
            print(f"[WAR DB ERROR] {_db_err}")

        payout_line = (
            f"↩️ **Bets returned**"
            if is_tie else
            f"💰 **Payout** • {format_amount(payout)} 💎"
        )
        description = (
            f"💰 **Bet** • {format_amount(self.bet)} 💎\
"
            f"\
"
            f"┌─────────────────────────┐\
"
            f"│ 🃏 **{self.creator.display_name}**\
"
            f"│ {war_card_str(creator_card)}\
"
            f"│\
"
            f"│ 🃏 **{opponent_name}**\
"
            f"│ {war_card_str(opponent_card)}\
"
            f"└─────────────────────────┘\
"
            f"\
"
            f"{payout_line}\
"
        )

        result_embed = discord.Embed(color=color, description=f"## ⚔️  WAR — {title}\n{result_desc(creator_won if not is_tie else False, is_tie, self.bet, payout)}")
        result_embed.add_field(name=f"🃏 {self.creator.display_name}", value=f"**{war_card_str(creator_card)}**", inline=True)
        result_embed.add_field(name=f"🃏 {opponent_name}",             value=f"**{war_card_str(opponent_card)}**", inline=True)
        result_embed.add_field(name="💰 Bet",    value=f"**{format_amount(self.bet)} 💎**",  inline=True)
        result_embed.add_field(name="🎁 Payout", value=f"**{format_amount(payout)} 💎**",   inline=True)
        result_embed.set_thumbnail(url=await get_avatar(self.creator))
        _brand_embed(result_embed)
        await asyncio.sleep(0.3)
        try:
            await msg.edit(embed=result_embed, view=None)
        except Exception as e:
            print(f'[RESULT DISPLAY FAILED] {e}')

        self.stop()
        log_e = discord.Embed(title="⚔️ War Result", color=color)
        log_e.add_field(name="Creator",  value=self.creator.mention,    inline=True)
        log_e.add_field(name="Opponent", value=opponent_label,           inline=True)
        log_e.add_field(name="Bet",      value=format_amount(self.bet),  inline=True)
        log_e.add_field(name="Outcome",  value=outcome_str,              inline=True)
        log_e.set_footer(text=now_ts())
        await send_log(log_e)

@bot.tree.command(name="war", description="Flip a card — highest card wins! Join, call bot, or start.")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M")
async def cmd_war(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("war", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(
            f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("war", interaction.user):
        await interaction.response.send_message(
            "🔒 **War** is currently locked to staff only.", ephemeral=True
        )
        return

    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)

    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view = WarView(interaction.user, amt)
    description = (
        f"💰 **Bet** • {format_amount(amt)} 💎\
"
        f"\
"
        f"┌─────────────────────────┐\
"
        f"│ 🃏 **{interaction.user.display_name}**\
"
        f"│ ?\
"
        f"│\
"
        f"│ 🃏 **Opponent**\
"
        f"│ ?\
"
        f"└─────────────────────────┘\
"
        f"\
"
        f"Waiting for opponent...\
"
    )
    embed = discord.Embed(
        color=C_GOLD,
        description=(
            f"## ⚔️  WAR\n"
            f"╔══════════════════════╗\n"
            f"║  Wager  {format_amount(amt):>14}  ║\n"
            f"╚══════════════════════╝\n"
            f"Draw a card — highest card wins **2×**.\n"
            f"Tie = both bets returned."
        )
    )
    embed.set_footer(text="Join  ·  vs Bot  ·  Start")
    await interaction.response.send_message(embed=embed, view=view)
    view._original_message = await interaction.original_response()

HILO_SUITS   = ["♠️", "♥️", "♦️", "♣️"]
HILO_RANKS   = {1: "A", 2: "2", 3: "3", 4: "4", 5: "5",
                6: "6", 7: "7", 8: "8", 9: "9", 10: "10",
                11: "J", 12: "Q", 13: "K"}
HILO_MULTS   = [1.136]  # flat 1.136x per correct round, compounding, capped at 15x total — 6% edge
HILO_MAX_MULT = 15.0

def hilo_card() -> tuple[int, str]:
    return (random.randint(1, 13), random.choice(HILO_SUITS))

def hilo_card_str(card: tuple[int, str]) -> str:
    rank, suit = card
    return f"`{HILO_RANKS[rank]}{suit}`"

def hilo_round_mult(round_num: int) -> float:
    """Not used — kept for reference. Cumulative mult uses 1.15 compound."""
    return 1.136

def hilo_cumulative_mult(rounds_won: int) -> float:
    """Total multiplier after winning `rounds_won` rounds, capped at HILO_MAX_MULT."""
    mult = round(1.136 ** rounds_won, 4)
    return min(mult, HILO_MAX_MULT)

def hilo_win_chance(current_rank: int, direction: str) -> float:
    """True probability of winning given current card and direction (for display only)."""
    if direction == "higher":
        winning = 13 - current_rank          # cards strictly higher
        tie     = 0                           # ties handled separately
        return round(winning / 13 * 100, 1)
    else:
        winning = current_rank - 1
        return round(winning / 13 * 100, 1)

class HiloView(BaseGameView):
    def __init__(self, creator: discord.User, bet: int,
                 current_card: tuple[int, str]):
        super().__init__(timeout=120)
        self.creator      = creator
        self.bet          = bet
        self.current_card = current_card
        self.rounds_won   = 0
        self.done         = False
        self.bet_deducted = False
        self._lock        = asyncio.Lock()
        self._original_message = None

    @property
    def current_mult(self) -> float:
        return hilo_cumulative_mult(self.rounds_won)

    @property
    def next_mult(self) -> float:
        return min(hilo_cumulative_mult(self.rounds_won + 1), HILO_MAX_MULT)

    @property
    def current_winnings(self) -> int:
        return int(self.bet * self.current_mult)

    @property
    def next_winnings(self) -> int:
        return int(self.bet * self.next_mult)

    def game_embed(self) -> discord.Embed:
        at_cap   = self.current_mult >= HILO_MAX_MULT
        card_str = hilo_card_str(self.current_card)
        mult_str = f"{self.current_mult:.1f}x{'  🏆 MAX' if at_cap else ''}"
        next_str = f"{format_amount(self.next_winnings)} 💎 ({self.next_mult:.1f}x)" if not at_cap else "MAX REACHED"
        guesses  = self.rounds_won
        guess_word = f"{guesses} Correct Guess{'es' if guesses != 1 else ''}"

        description = (
            f"💰 **Bet** • {format_amount(self.bet)} 💎\
"
            f"📊 **Multiplier** • {mult_str}\
"
            f"\
"
            f"┌─────────────────────────┐\
"
            f"│ 🎴 **Current Card**\
"
            f"│ {card_str}\
"
            f"│\
"
            f"│ ❓ **Next Card**\
"
            f"│ ?\
"
            f"└─────────────────────────┘\
"
            f"\
"
            f"💵 **Next Guess** • {next_str}\
"
        )
        embed = discord.Embed(color=C_GOLD, description=f"## 🃏  HI-LO\n{description}")
        embed.set_footer(text=f"🎯 {guess_word} • Will the next card be higher or lower?")
        return embed

    async def _deduct_bet(self) -> bool:
        if self.bet_deducted:
            return True
        self.bet_deducted = True
        async with get_user_lock(self.creator.id):
            conn = await get_conn()
            try:
                return await deduct_balance_safe(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)

    async def _guess(self, interaction: discord.Interaction, direction: str):
        async with self._lock:
            if self.done:
                await interaction.response.send_message("❌ Game already over.", ephemeral=True)
                return

        await interaction.response.defer()

        async with self._lock:
            if not await self._deduct_bet():
                await interaction.followup.send(
                    "❌ Insufficient balance. Game cancelled.", ephemeral=True)
                self.done = True
                self.stop()
                return

            prev_card  = self.current_card
            prev_rank  = prev_card[0]

            _hilo_forced = _force_result.pop(self.creator.id, None)
            if _hilo_forced == "win":
                player_wins = True
            elif _hilo_forced == "lose":
                player_wins = False
            else:
                player_wins = random.random() >= BOT_HOUSE_WIN  # 48% player wins

            if direction == "higher":
                valid_win  = list(range(prev_rank + 1, 14))
                valid_lose = list(range(1, prev_rank))
            elif direction == "lower":
                valid_win  = list(range(1, prev_rank))
                valid_lose = list(range(prev_rank + 1, 14))
            else:  # same
                valid_win  = [prev_rank]
                valid_lose = [r for r in range(1, 14) if r != prev_rank]

            if player_wins and valid_win:
                new_rank = random.choice(valid_win)
            elif not player_wins and valid_lose:
                new_rank = random.choice(valid_lose)
            else:
                new_rank = random.randint(1, 13)

            new_card = (new_rank, random.choice(["♠", "♥", "♦", "♣"]))

            if direction == "same":
                won_round = (new_rank == prev_rank)
                is_tie    = False
            else:
                is_tie    = (new_rank == prev_rank)
                won_round = (
                    (direction == "higher" and new_rank > prev_rank) or
                    (direction == "lower"  and new_rank < prev_rank)
                )

            if is_tie:
                self.current_card = new_card
                await interaction.edit_original_response(embed=self.game_embed(), view=self)
                return

            if won_round:
                self.rounds_won  += 1
                self.current_card = new_card
                await interaction.edit_original_response(embed=self.game_embed(), view=self)
            else:
                self.done = True
                self.stop()

                guesses    = self.rounds_won
                guess_word = f"{guesses} Correct Guess{'es' if guesses != 1 else ''}"
                lose_desc  = (
                    f"💰 **Bet** — {format_amount(self.bet)} 💎\n"
                    f"📊 **Multiplier** — {self.current_mult:.2f}x\n"
                    f"💔 **Loss** — {format_amount(self.bet)} 💎\n"
                    f"🎯 **Correct Guesses** — {guesses}\n"
                    f"\n"
                    f"Your Card: {hilo_card_str(prev_card)}  →  Next: {hilo_card_str(new_card)}"
                )
                lose_embed = discord.Embed(
                    color=C_LOSS,
                    description=f"## ✗  WRONG GUESS!\n{lose_desc}"
                )
                _brand_embed(lose_embed)

                conn = await get_conn()
                try:
                    await record_game(conn, self.creator.id, False, self.bet, 0, game="hilo")
                    await log_transaction(conn, self.creator.id, "hilo_loss", -self.bet)
                    _rank_guild = interaction.guild or bot.get_guild(GUILD_ID)
                    if _rank_guild:
                        row = await get_user(conn, self.creator.id)
                        member = _rank_guild.get_member(self.creator.id)
                        if row and member:
                            await update_user_rank(member, row["wagered"])
                finally:
                    await release_conn(conn)

                try:
                    await interaction.edit_original_response(embed=lose_embed, view=None)
                except Exception as _result_err:
                    print(f'[RESULT DISPLAY FAILED] {type(_result_err).__name__}: {_result_err}')

                log_e = discord.Embed(title="🃏 HiLo Result", color=C_LOSS)
                log_e.add_field(name="Player",     value=self.creator.mention,    inline=True)
                log_e.add_field(name="Bet",        value=format_amount(self.bet), inline=True)
                log_e.add_field(name="Rounds Won", value=str(self.rounds_won),    inline=True)
                log_e.add_field(name="Outcome",    value="❌ LOSS",               inline=True)
                log_e.set_footer(text=now_ts())
                await send_log(log_e)

    async def _cashout(self, interaction: discord.Interaction):
        async with self._lock:
            if self.done:
                await interaction.response.send_message("❌ Game already over.", ephemeral=True)
                return
            if self.rounds_won == 0:
                await interaction.response.send_message(
                    "❌ You must guess at least once before cashing out.", ephemeral=True)
                return
            self.done = True
            self.stop()

        await interaction.response.defer()

        async with self._lock:
            if not self.bet_deducted:
                if not await self._deduct_bet():
                    await interaction.followup.send(
                        "❌ Insufficient balance. Game cancelled.", ephemeral=True)
                    return

            payout = min(self.current_winnings, MAX_PAYOUT)
            net    = payout - self.bet

            conn = await get_conn()
            try:
                payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "hilo")
                await record_game(conn, self.creator.id, True, self.bet, payout, game="hilo")

                await conn.execute(
                    """INSERT INTO user_stats (user_id, hilo_cashouts) VALUES ($1, 1)
                       ON CONFLICT (user_id) DO UPDATE SET hilo_cashouts = user_stats.hilo_cashouts + 1""",
                    str(self.creator.id)
                )
                await log_transaction(conn, self.creator.id, "hilo_cashout", net)
                if interaction.guild:
                    row = await get_user(conn, self.creator.id)
                    member = interaction.guild.get_member(self.creator.id)
                    if row and member:
                        await update_user_rank(member, row["wagered"])
                    asyncio.create_task(check_vip_balance(interaction.user.id if hasattr(interaction, 'user') else self.creator.id, interaction.guild if hasattr(interaction, 'guild') else None))
            finally:
                await release_conn(conn)

            guesses    = self.rounds_won
            guess_word = f"{guesses} Correct Guess{'es' if guesses != 1 else ''}"
            win_desc   = (
                f"💰 **Bet** — {format_amount(self.bet)} 💎\n"
                f"📊 **Multiplier** — {self.current_mult:.2f}x\n"
                f"🏆 **Payout** — {format_amount(payout)} 💎\n"
                f"🎯 **Correct Guesses** — {guesses}"
            )
            win_embed = discord.Embed(
                color=C_WIN,
                description=f"## 🎴  HI-LO — CASHED OUT\n{win_desc}"
            )
            _brand_embed(win_embed)

            try:
                await interaction.edit_original_response(embed=win_embed, view=None)
            except Exception as _result_err:
                print(f'[RESULT DISPLAY FAILED] {type(_result_err).__name__}: {_result_err}')

            log_e = discord.Embed(title="🃏 HiLo Result", color=C_WIN)
            log_e.add_field(name="Player",     value=self.creator.mention,        inline=True)
            log_e.add_field(name="Bet",        value=format_amount(self.bet),     inline=True)
            log_e.add_field(name="Multiplier", value=f"{self.current_mult:.2f}x", inline=True)
            log_e.add_field(name="Payout",     value=format_amount(payout),       inline=True)
            log_e.add_field(name="Rounds Won", value=str(self.rounds_won),        inline=True)
            log_e.add_field(name="Outcome",    value="✅ CASHOUT",                inline=True)
            log_e.set_footer(text=now_ts())
            await send_log(log_e)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.done:
            conn = await get_conn()
            try:
                if self.rounds_won > 0:
                    payout = min(self.current_winnings, MAX_PAYOUT)
                    payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "hilo")
                    await record_game(conn, self.creator.id, True, self.bet, payout, game="hilo")
                    await log_transaction(conn, self.creator.id, "hilo_timeout_cashout", payout - self.bet)
                    desc = f"Game timed out — auto cashed out **{format_amount(payout)} 💎** ({self.rounds_won} correct guess{'es' if self.rounds_won != 1 else ''})."
                else:
                    await update_balance(conn, self.creator.id, self.bet)
                    desc = f"Game timed out — bet of **{format_amount(self.bet)}** refunded."
            finally:
                await release_conn(conn)
        try:
                await self._original_message.edit(
                    embed=discord.Embed(color=C_DARK, description=f"## 🃏  HI-LO — EXPIRED\n> {desc}"),
                    view=None)
        except Exception as e:
                print(f"[ERROR] {type(e).__name__}: {e}")
        await super().on_timeout()

    @discord.ui.button(label="✅ Higher", style=discord.ButtonStyle.green)
    async def higher_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._guess(interaction, "higher")

    @discord.ui.button(label="📉 Lower", style=discord.ButtonStyle.danger)
    async def lower_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._guess(interaction, "lower")

    @discord.ui.button(label="〰️ Same", style=discord.ButtonStyle.blurple)
    async def same_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._guess(interaction, "same")

    @discord.ui.button(label="💰 Cashout", style=discord.ButtonStyle.secondary)
    async def cashout_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._cashout(interaction)

@bot.tree.command(name="hilo", description="Play Higher or Lower — chain correct guesses to multiply your bet!")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M")
async def cmd_hilo(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("hilo", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(
            f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("hilo", interaction.user):
        await interaction.response.send_message(
            "🔒 **Hilo** is currently locked to staff only.", ephemeral=True
        )
        return

    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)

    first_card = hilo_card()
    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view       = HiloView(interaction.user, amt, first_card)
    view.bet_deducted = True

    embed = view.game_embed()
    await interaction.response.send_message(embed=embed, view=view)
    view._original_message = await interaction.original_response()

TOWER_ROWS    = 10
TOWER_COLS    = 3
TOWER_SAFE    = 2   # safe tiles per row (1 bomb)
TOWER_ROW_MULTS = [1.175, 1.175, 1.1946, 1.1946, 1.2142, 1.2142, 1.2338, 1.2338, 1.2534, 1.273]  # 6% edge

def tower_cumulative_mult(rows_cleared: int) -> float:
    mult = 1.0
    for i in range(rows_cleared):
        mult *= TOWER_ROW_MULTS[min(i, len(TOWER_ROW_MULTS) - 1)]
    return round(mult, 4)

def generate_tower() -> list[list[str]]:
    """Generate the full tower. Each row: 2 safe + 1 bomb, shuffled."""
    tower = []
    for _ in range(TOWER_ROWS):
        row = ["✅", "✅", "❌"]
        random.shuffle(row)
        tower.append(row)
    return tower

def render_tower(tower: list, current_row: int, revealed: dict) -> str:
    """
    Render tower from top to bottom matching bloxysab style.
    Revealed rows show picked tile (✅/❌) and hide others as ⬛.
    Current row shows ⬛ ⬛ ⬛ (pickable).
    Future rows show ⬛ ⬛ ⬛.
    """
    lines = []
    for r in range(TOWER_ROWS - 1, -1, -1):
        row_num = r + 1
        if r in revealed:
            picked_col = revealed[r]
            cols = []
            for c in range(TOWER_COLS):
                if c == picked_col:
                    cols.append(tower[r][c])  # ✅ or ❌
                else:
                    cols.append("⬛")
            lines.append(f"Row {row_num}: {''.join(cols)}")
        elif r == current_row:
            lines.append(f"Row {row_num}: ⬛⬛⬛")
        else:
            lines.append(f"Row {row_num}: ⬛⬛⬛")
    return "\
".join(lines)

_TW_FONT_BOLD   = "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"
_TW_FONT_REG    = "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"

class TowersView(BaseGameView):
    def __init__(self, creator: discord.User, bet: int, tower: list):
        super().__init__(timeout=180)
        self.creator       = creator
        self.bet           = bet
        self.tower         = tower
        self.current_row   = 0
        self.rows_cleared  = 0
        self.revealed      = {}
        self.done          = False
        self.bet_deducted  = False
        self._lock         = asyncio.Lock()
        self._original_message = None
        try:
            self._update_buttons()
        except Exception:
            pass  # buttons not yet registered on first __init__ call

    @property
    def current_mult(self) -> float:
        return tower_cumulative_mult(self.rows_cleared)

    @property
    def next_mult(self) -> float:
        return tower_cumulative_mult(self.rows_cleared + 1)

    @property
    def current_winnings(self) -> int:
        return int(self.bet * self.current_mult)

    @property
    def next_winnings(self) -> int:
        return int(self.bet * self.next_mult)

    def _update_buttons(self):
        self.col0_btn.disabled    = self.done
        self.col1_btn.disabled    = self.done
        self.col2_btn.disabled    = self.done
        self.cashout_btn.disabled = self.done or self.rows_cleared == 0

    def game_embed(self, outcome: str = "playing") -> discord.Embed:
        if outcome == "playing":
            color = C_BLUE
            title = "🗼  Towers"
        elif outcome == "win":
            color = C_WIN
            title = "🗼  Towers - Cashed Out"
        elif outcome == "bomb":
            color = C_LOSS
            title = "🗼  Towers - 💥 Boom"
        else:
            color = C_VIP
            title = "🗼  Towers - Cleared!"

        grid        = render_tower(self.tower, self.current_row, self.revealed)
        payout      = min(self.current_winnings, MAX_PAYOUT)
        description = (
            f"{grid}\n\n"
            f"Bet: **{format_amount(self.bet)}** 💎\n"
            f"Multiplier: **{self.current_mult:.2f}x**\n"
            f"Potential Winnings: **{format_amount(payout)}** 💎\n"
        )
        embed = discord.Embed(color=color, title=title, description=description)
        embed.set_footer(text=f"Row {self.current_row + 1} • Easy Mode")
        return embed

    async def _deduct_bet(self) -> bool:
        if self.bet_deducted:
            return True
        self.bet_deducted = True
        async with get_user_lock(self.creator.id):
            conn = await get_conn()
            try:
                return await deduct_balance_safe(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)

    async def _pick(self, interaction: discord.Interaction, col: int):
        async with self._lock:
            if self.done:
                await interaction.response.send_message("❌ Game already over.", ephemeral=True)
                return

        await interaction.response.defer()

        async with self._lock:
            if not await self._deduct_bet():
                await interaction.followup.send("❌ Insufficient balance. Game cancelled.", ephemeral=True)
                self.done = True
                self.stop()
                return

            tile = self.tower[self.current_row][col]
            self.revealed[self.current_row] = col

            _tw_forced = _force_result.pop(self.creator.id, None)
            if _tw_forced == "win":
                tile = "✅"   # always safe
            elif _tw_forced == "lose":
                tile = "❌"   # always bomb

            if tile == "❌":
                self.done = True
                self.stop()
                self._update_buttons()

                conn = await get_conn()
                try:
                    await record_game(conn, self.creator.id, False, self.bet, 0, "towers")
                    await log_transaction(conn, self.creator.id, "towers_loss", -self.bet)
                    _rank_guild = interaction.guild or bot.get_guild(GUILD_ID)
                    if _rank_guild:
                        row = await get_user(conn, self.creator.id)
                        member = _rank_guild.get_member(self.creator.id)
                        if row and member:
                            await update_user_rank(member, row["wagered"])
                finally:
                    await release_conn(conn)

                try:
                    await interaction.edit_original_response(embed=self.game_embed("bomb"), view=None)
                except Exception as _result_err:
                    print(f'[RESULT DISPLAY FAILED] {type(_result_err).__name__}: {_result_err}')

                log_e = discord.Embed(title="🏰 Towers Result", color=C_LOSS)
                log_e.add_field(name="Player",       value=self.creator.mention,    inline=True)
                log_e.add_field(name="Bet",          value=format_amount(self.bet), inline=True)
                log_e.add_field(name="Rows Cleared", value=str(self.rows_cleared),  inline=True)
                log_e.add_field(name="Outcome",      value="💣 BOMB",               inline=True)
                log_e.set_footer(text=now_ts())
                await send_log(log_e)

            else:
                self.rows_cleared += 1
                self.current_row  += 1

                if self.rows_cleared == TOWER_ROWS:
                    self.done = True
                    self.stop()
                    self._update_buttons()
                    payout = min(self.current_winnings, MAX_PAYOUT)
                    net    = payout - self.bet

                    conn = await get_conn()
                    try:
                        payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "towers")
                        await record_game(conn, self.creator.id, True, self.bet, payout)
                        await log_transaction(conn, self.creator.id, "towers_clear", net)
                        await conn.execute(
                            """INSERT INTO user_stats (user_id, towers_clears) VALUES ($1, 1)
                               ON CONFLICT (user_id) DO UPDATE SET towers_clears = user_stats.towers_clears + 1""",
                            str(self.creator.id)
                        )
                        await conn.execute(
                            """INSERT INTO user_stats (user_id, towers_cashouts) VALUES ($1, 1)
                               ON CONFLICT (user_id) DO UPDATE SET towers_cashouts = user_stats.towers_cashouts + 1""",
                            str(self.creator.id)
                        )
                        if interaction.guild:
                            row = await get_user(conn, self.creator.id)
                            member = interaction.guild.get_member(self.creator.id)
                            if row and member:
                                await update_user_rank(member, row["wagered"])
                    finally:
                        await release_conn(conn)

                    try:
                        await interaction.edit_original_response(embed=self.game_embed("cleared"), view=None)
                    except Exception as _result_err:
                        print(f'[RESULT DISPLAY FAILED] {type(_result_err).__name__}: {_result_err}')

                    log_e = discord.Embed(title="🏰 Towers Result", color=C_VIP)
                    log_e.add_field(name="Player",  value=self.creator.mention,        inline=True)
                    log_e.add_field(name="Bet",     value=format_amount(self.bet),     inline=True)
                    log_e.add_field(name="Payout",  value=format_amount(payout),       inline=True)
                    log_e.add_field(name="Outcome", value="🏆 TOWER CLEARED",          inline=True)
                    log_e.set_footer(text=now_ts())
                    await send_log(log_e)
                else:
                    self._update_buttons()
                    await interaction.edit_original_response(embed=self.game_embed("playing"), view=self)

    async def _cashout(self, interaction: discord.Interaction):
        async with self._lock:
            if self.done:
                await interaction.response.send_message("❌ Game already over.", ephemeral=True)
                return
            if self.rows_cleared == 0:
                await interaction.response.send_message(
                    "❌ Clear at least one row before cashing out.", ephemeral=True)
                return
            if not await self._deduct_bet():
                await interaction.response.send_message(
                    "❌ Insufficient balance. Game cancelled.", ephemeral=True)
                self.done = True
                self.stop()
                return

            self.done = True
            self.stop()
            self._update_buttons()

            payout = min(self.current_winnings, MAX_PAYOUT)
            net    = payout - self.bet
            await interaction.response.defer()

            conn = await get_conn()
            try:
                payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "towers")
                await record_game(conn, self.creator.id, True, self.bet, payout)
                await log_transaction(conn, self.creator.id, "towers_cashout", net)
                await conn.execute(
                    """INSERT INTO user_stats (user_id, towers_cashouts) VALUES ($1, 1)
                       ON CONFLICT (user_id) DO UPDATE SET towers_cashouts = user_stats.towers_cashouts + 1""",
                    str(self.creator.id)
                )
                if interaction.guild:
                    row = await get_user(conn, self.creator.id)
                    member = interaction.guild.get_member(self.creator.id)
                    if row and member:
                        await update_user_rank(member, row["wagered"])
                    asyncio.create_task(check_vip_balance(interaction.user.id if hasattr(interaction, 'user') else self.creator.id, interaction.guild if hasattr(interaction, 'guild') else None))
            finally:
                await release_conn(conn)

            try:
                await interaction.edit_original_response(embed=self.game_embed("win"), view=None)
            except Exception as _result_err:
                print(f'[RESULT DISPLAY FAILED] {type(_result_err).__name__}: {_result_err}')

            log_e = discord.Embed(title="🏰 Towers Result", color=C_WIN)
            log_e.add_field(name="Player",       value=self.creator.mention,        inline=True)
            log_e.add_field(name="Bet",          value=format_amount(self.bet),     inline=True)
            log_e.add_field(name="Rows Cleared", value=str(self.rows_cleared),      inline=True)
            log_e.add_field(name="Multiplier",   value=f"{self.current_mult:.2f}x", inline=True)
            log_e.add_field(name="Payout",       value=format_amount(payout),       inline=True)
            log_e.add_field(name="Outcome",      value="✅ CASHOUT",                inline=True)
            log_e.set_footer(text=now_ts())
            await send_log(log_e)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.done:
            conn = await get_conn()
            try:
                if self.rows_cleared > 0:
                    payout = min(self.current_winnings, MAX_PAYOUT)
                    payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "towers")
                    await record_game(conn, self.creator.id, True, self.bet, payout)
                    await log_transaction(conn, self.creator.id, "towers_timeout_cashout", payout - self.bet)
                    await conn.execute(
                        """INSERT INTO user_stats (user_id, towers_cashouts) VALUES ($1, 1)
                           ON CONFLICT (user_id) DO UPDATE SET towers_cashouts = user_stats.towers_cashouts + 1""",
                        str(self.creator.id)
                    )
                    desc = f"Game timed out — auto cashed out **{format_amount(payout)} 💎** ({self.rows_cleared} rows cleared)."
                else:
                    await update_balance(conn, self.creator.id, self.bet)
                    desc = f"Game timed out — bet of **{format_amount(self.bet)}** refunded."
            finally:
                await release_conn(conn)
            try:
                await self._original_message.edit(
                    embed=discord.Embed(color=C_DARK, description=f"## 🏰  TOWERS — EXPIRED\n> {desc}"),
                    view=None)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
        await super().on_timeout()

    @discord.ui.button(label="1", style=discord.ButtonStyle.blurple)
    async def col0_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._pick(interaction, 0)

    @discord.ui.button(label="2", style=discord.ButtonStyle.blurple)
    async def col1_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._pick(interaction, 1)

    @discord.ui.button(label="3", style=discord.ButtonStyle.blurple)
    async def col2_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._pick(interaction, 2)

    @discord.ui.button(label="💰 Cashout", style=discord.ButtonStyle.green, row=1)
    async def cashout_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        await self._cashout(interaction)

@bot.tree.command(name="towers", description="Climb the tower — pick safe tiles to multiply your bet!")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M")
async def cmd_towers(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("towers", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(
            f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("towers", interaction.user):
        await interaction.response.send_message(
            "🔒 **Towers** is currently locked to staff only.", ephemeral=True
        )
        return

    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)

    tower = generate_tower()
    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view  = TowersView(interaction.user, amt, tower)
    view.bet_deducted = True
    view._update_buttons()
    _init_embed = view.game_embed()
    await interaction.response.send_message(embed=_init_embed, view=view)
    view._original_message = await interaction.original_response()

RPS_MOVES    = ["rock", "paper", "scissors"]
RPS_EMOJI    = {"rock": "✊", "paper": "✋", "scissors": "✌️"}
RPS_LABEL    = {"rock": "Rock", "paper": "Paper", "scissors": "Scissors"}
RPS_BEATS    = {"rock": "scissors", "paper": "rock", "scissors": "paper"}
RPS_WIN_MULT = 1.94
RPS_MAX_MULT = 50.0

def rps_outcome(player: str, bot_pick: str) -> str:
    if player == bot_pick:
        return "tie"
    if RPS_BEATS[player] == bot_pick:
        return "win"
    return "loss"

def rps_cumulative_mult(wins: int) -> float:
    return round(min(RPS_WIN_MULT ** wins, RPS_MAX_MULT), 4)

_RPS_FONT_BOLD  = "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"
_RPS_FONT_HAND  = "/usr/share/fonts/opentype/unifont/unifont.otf"
_RPS_HAND_SYM   = {"rock": "\u270a", "paper": "\u270b", "scissors": "\u270c"}

_RPS_BG          = (17,  18,  23)
_RPS_CARD_BG     = (30,  31,  40)
_RPS_CARD_EMPTY  = (22,  23,  30)
_RPS_WIN_C       = (34, 197,  94)
_RPS_LOSS_C      = (239, 68,  68)
_RPS_TIE_C       = (234,179,   8)
_RPS_EMPTY_C     = (55,  58,  80)
_RPS_WHITE       = (255,255, 255)
_RPS_DARK        = (10,  10,  10)
_RPS_MUTED       = (120,120, 150)

_CARD_W = 90; _CARD_H = 100; _CARD_R = 12; _BADGE_H = 22
_GAP    = 10; _PAD_X  = 18;  _PAD_Y  = 18
_ROW_GAP= 14; _LABEL_H= 26;  _MAX_COLS = 6

def _rr(draw, xy, r, fill, outline, w=3):
    draw.rounded_rectangle(xy, radius=r, fill=fill, outline=outline, width=w)

def rps_card_grid(history: list) -> str:
    """Fallback text grid used only if Pillow is unavailable."""
    if not history:
        return ""
    lines = []
    for i, h in enumerate(history, 1):
        p, b, res, mult = h["player"], h["bot"], h["result"], h["mult"]
        badge = "✅ **WIN**" if res=="win" else "❌ **LOSE**" if res=="loss" else "🤝 **TIE**"
        lines.append(f"`R{i:02}` {RPS_EMOJI[p]} **vs** {RPS_EMOJI[b]}  \u00b7  {badge}  \u00b7  `{mult:.2f}x`")
    return "\n".join(lines)

async def cmd_rps(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("rps", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(
            f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("rps", interaction.user):
        await interaction.response.send_message(
            "🔒 **RPS** is currently locked to staff only.", ephemeral=True)
        return
    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return
    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)
    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view = RPSView(interaction.user, amt)
    view.bet_deducted = True
    _init_embed = view.game_embed()
    await interaction.response.send_message(embed=_init_embed, view=view)
    view._original_message = await interaction.original_response()

MINES_MAX_MULT  = 5000.0
MINES_GRID_SIZE = 25

def mines_dynamic_factor(mines: int) -> float:
    """
    Per-mine-count multiplier factor. Must always be > (safe/total) so the
    multiplier grows with every gem click. Values below 1.0 apply house edge.
    """
    safe = MINES_GRID_SIZE - mines
    if safe <= 0:
        return 0.01
    if mines == 1:
        return 0.982
    elif mines <= 3:
        return 0.95
    elif mines <= 10:
        return 0.92
    else:
        return 0.89

def mines_calc_mult(mines: int, gems_found: int) -> float:
    if gems_found == 0:
        return 1.0
    total  = MINES_GRID_SIZE
    safe   = total - mines
    factor = mines_dynamic_factor(mines)
    mult   = 1.0
    for i in range(gems_found):
        remaining_tiles = total - i
        remaining_safe  = safe - i
        if remaining_tiles <= 0 or remaining_safe <= 0:
            break
        prob  = remaining_safe / remaining_tiles
        mult *= (1.0 / prob) * factor
    return round(min(mult, MINES_MAX_MULT), 2)

_MINES_DANGER_WEIGHTS = [
    1,2,3,2,1,
    2,4,6,4,2,
    3,6,9,6,3,
    2,4,6,4,2,
    1,2,3,2,1,
]  # center-heavy: index 12 (center) = weight 9

def mines_generate_grid(mines: int, force_win: bool = False) -> list:
    """Generate initial grid. Rigging happens per-click in MinesView._pick."""
    grid = ["gem"] * MINES_GRID_SIZE
    if force_win:
        bomb_positions = list(range(MINES_GRID_SIZE - mines, MINES_GRID_SIZE))
    else:
        bomb_positions = random.sample(range(MINES_GRID_SIZE), mines)
    for i in bomb_positions:
        grid[i] = "bomb"
    return grid

def mines_rig_board(grid: list, revealed: set, last_clicked: int, mines: int) -> list:
    """
    Fully rigged board — after every safe click, bombs cluster toward
    the tiles MOST LIKELY to be clicked next (adjacent + natural click paths).
    Uses weighted sampling without replacement for correct mine count.
    """
    unrevealed = [i for i in range(MINES_GRID_SIZE) if i not in revealed]
    if len(unrevealed) <= mines:
        return grid

    r_c, c_c = divmod(last_clicked, 5)

    def weight(idx):
        r, c = divmod(idx, 5)
        dist  = abs(r - r_c) + abs(c - c_c)
        base  = _MINES_DANGER_WEIGHTS[idx]
        if dist == 0:  return 0    # already revealed — never place bomb here
        if dist == 1:  return base + 20   # immediately adjacent — very dangerous
        if dist == 2:  return base + 10   # two hops away
        if dist == 3:  return base + 3
        return max(base - 3, 1)

    weights = [weight(i) for i in unrevealed]
    total   = sum(weights)
    # Weighted sampling WITHOUT replacement
    chosen  = []
    pool    = list(zip(unrevealed, weights))
    for _ in range(min(mines, len(pool))):
        if not pool: break
        t = random.uniform(0, sum(w for _, w in pool))
        cum = 0
        for j, (tile, w) in enumerate(pool):
            cum += w
            if cum >= t:
                chosen.append(tile)
                pool.pop(j)
                break

    new_grid = ["gem"] * MINES_GRID_SIZE
    for b in chosen:
        new_grid[b] = "bomb"
    for r in revealed:
        new_grid[r] = "gem"
    return new_grid

def mines_render_grid(grid: list, revealed: set, game_over: bool = False) -> str:
    rows = []
    for r in range(5):
        row_str = ""
        for c in range(5):
            idx = r * 5 + c
            if idx in revealed:
                row_str += "💎"
            elif game_over and grid[idx] == "bomb":
                row_str += "💣"
            else:
                row_str += "⬛"
        rows.append(row_str)
    return "\
".join(rows)

class MinesView(BaseGameView):
    def __init__(self, creator: discord.User, bet: int, mines: int):
        super().__init__(timeout=180)
        self.creator      = creator
        self.bet          = bet
        self.mines        = mines
        self.grid         = mines_generate_grid(mines)
        self.revealed     = set()
        self.gems_found   = 0
        self.done         = False
        self.bet_deducted = False
        self._lock        = asyncio.Lock()
        self._original_message = None
        self._build_buttons()

    @property
    def current_mult(self) -> float:
        return mines_calc_mult(self.mines, self.gems_found)

    @property
    def current_winnings(self) -> int:
        return int(self.bet * self.current_mult)

    def _build_buttons(self):
        self.clear_items()
        for i in range(MINES_GRID_SIZE):
            row_num     = i // 5
            is_revealed = i in self.revealed
            btn = discord.ui.Button(
                label="💎" if is_revealed else "\​",
                style=discord.ButtonStyle.success if is_revealed else discord.ButtonStyle.secondary,
                custom_id=f"mine_{i}",
                row=row_num,
                disabled=self.done
            )
            btn.callback = self._make_callback(i, is_revealed)
            self.add_item(btn)

    def _make_callback(self, index: int, is_revealed: bool):
        async def callback(interaction: discord.Interaction):
            if interaction.user.id != self.creator.id:
                await interaction.response.send_message("Not your game.", ephemeral=True)
                return
            if is_revealed:
                await self._cashout(interaction)
            else:
                await self._pick(interaction, index)
        return callback

    def game_embed(self, outcome: str = "playing") -> discord.Embed:
        gems_total = MINES_GRID_SIZE - self.mines
        colors     = {"playing": C_BLUE, "win": C_WIN, "loss": C_LOSS, "cleared": 0xFFD700}
        color      = colors.get(outcome, C_BLUE)
        game_over  = outcome in ("win", "loss", "cleared")
        payout     = self.current_winnings
        profit     = payout - self.bet
        profit_str = f"+{format_amount(profit)}" if profit >= 0 else f"-{format_amount(abs(profit))}"
        grid_str   = mines_render_grid(self.grid, self.revealed, game_over=game_over)

        if outcome == "loss":
            stats = (
                f"## 💥  MINES — BOOM!\n"
                f"┌─────────────────────────┐\n"
                f"💰 **Bet** — {format_amount(self.bet)} 💎\n"
                f"💣 **Mines** — {self.mines}\n"
                f"💎 **Found** — {self.gems_found}/{gems_total}\n"
                f"❌ **Lost** — {format_amount(self.bet)} 💎"
            )
        elif outcome in ("win", "cleared"):
            title_line = "## 🎉  VICTORY!" if outcome == "win" else "## 🏆  ALL CLEAR!"
            stats = (
                f"{title_line}\n"
                f"💰 **Bet** — {format_amount(self.bet)} 💎\n"
                f"📊 **Multiplier** — {self.current_mult:.2f}x\n"
                f"✨ **Profit** — {profit_str} 💎\n"
                f"💎 **Gems Found** — {self.gems_found}/{gems_total}"
            )
        else:
            next_mult   = mines_calc_mult(self.mines, self.gems_found + 1)
            cashout_tip = "\n💡 *Tap any revealed 💎 to cash out*" if self.gems_found > 0 else ""
            stats = (
                f"## 💣  MINES\n"
                f"💰 **Bet** — {format_amount(self.bet)} 💎\n"
                f"📊 **Multiplier** — {self.current_mult:.2f}x\n"
                f"💵 **Cashout now** — {format_amount(payout)} 💎\n"
                f"➡️ **Next gem** — {next_mult:.2f}x\n"
                f"💎 **Found** — {self.gems_found}/{gems_total}{cashout_tip}"
            )

        embed = discord.Embed(color=color, description=f"{stats}\n\n{grid_str}")
        embed.set_footer(text=f"💣 {self.mines} Mines  •  {'Game Ended' if game_over else 'Pick a tile!'}")
        return embed
    async def _deduct_bet(self) -> bool:
        if self.bet_deducted:
            return True
        self.bet_deducted = True
        async with get_user_lock(self.creator.id):
            conn = await get_conn()
            try:
                return await deduct_balance_safe(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)

    async def _pick(self, interaction: discord.Interaction, index: int):
        async with self._lock:
            if self.done or index in self.revealed:
                await interaction.response.send_message("Already revealed.", ephemeral=True)
                return

        await interaction.response.defer()

        async with self._lock:
            if not await self._deduct_bet():
                await interaction.followup.send("❌ Insufficient balance.", ephemeral=True)
                self.done = True
                self.stop()
                return
            tile = self.grid[index]

            _mn_forced = _force_result.pop(self.creator.id, None)
            if _mn_forced == "win":
                tile = "gem"   # always safe
            elif _mn_forced == "lose":
                tile = "bomb"  # always explode

            if tile == "bomb":
                self.done = True
                self.stop()
                self._build_buttons()
                conn = await get_conn()
                try:
                    await record_game(conn, self.creator.id, False, self.bet, 0, game="mines")
                    await log_transaction(conn, self.creator.id, "mines_loss", -self.bet)
                    _rank_guild = interaction.guild or bot.get_guild(GUILD_ID)
                    if _rank_guild:
                        row = await get_user(conn, self.creator.id)
                        member = _rank_guild.get_member(self.creator.id)
                        if row and member:
                            await update_user_rank(member, row["wagered"])
                finally:
                    await release_conn(conn)
                try:
                    await interaction.edit_original_response(embed=self.game_embed("loss"), view=None)
                except Exception as _result_err:
                    print(f'[RESULT DISPLAY FAILED] {type(_result_err).__name__}: {_result_err}')
                log_e = discord.Embed(title="💣 Mines Result", color=C_LOSS)
                log_e.add_field(name="Player",     value=self.creator.mention,    inline=True)
                log_e.add_field(name="Bet",        value=format_amount(self.bet), inline=True)
                log_e.add_field(name="Mines",      value=str(self.mines),         inline=True)
                log_e.add_field(name="Gems Found", value=str(self.gems_found),    inline=True)
                log_e.add_field(name="Outcome",    value="💥 BOOM",               inline=True)
                log_e.set_footer(text=now_ts())
                await send_log(log_e)

            else:
                self.revealed.add(index)
                self.gems_found += 1

                if not self.done:
                    self.grid = mines_rig_board(self.grid, self.revealed, index, self.mines)

                gems_total = MINES_GRID_SIZE - self.mines

                if self.gems_found >= gems_total:
                    self.done = True
                    self.stop()
                    payout = min(self.current_winnings, MAX_PAYOUT)
                    conn = await get_conn()
                    try:
                        payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "mines")
                        await record_game(conn, self.creator.id, True, self.bet, payout, game="mines")
                        await log_transaction(conn, self.creator.id, "mines_clear", payout - self.bet)
                        await conn.execute(
                            """INSERT INTO user_stats (user_id, mines_clears) VALUES ($1, 1)
                               ON CONFLICT (user_id) DO UPDATE SET mines_clears = user_stats.mines_clears + 1""",
                            str(self.creator.id)
                        )
                        await conn.execute(
                            """INSERT INTO user_stats (user_id, mines_cashouts) VALUES ($1, 1)
                               ON CONFLICT (user_id) DO UPDATE SET mines_cashouts = user_stats.mines_cashouts + 1""",
                            str(self.creator.id)
                        )
                        if interaction.guild:
                            row = await get_user(conn, self.creator.id)
                            member = interaction.guild.get_member(self.creator.id)
                            if row and member:
                                await update_user_rank(member, row["wagered"])
                    finally:
                        await release_conn(conn)
                    try:
                        await interaction.edit_original_response(embed=self.game_embed("cleared"), view=None)
                    except Exception as _result_err:
                        print(f'[RESULT DISPLAY FAILED] {type(_result_err).__name__}: {_result_err}')
                    log_e = discord.Embed(title="💣 Mines Result", color=C_VIP)
                    log_e.add_field(name="Player",  value=self.creator.mention,              inline=True)
                    log_e.add_field(name="Bet",     value=format_amount(self.bet),           inline=True)
                    log_e.add_field(name="Payout",  value=format_amount(payout),             inline=True)
                    log_e.add_field(name="Outcome", value="🏆 BOARD CLEARED",                inline=True)
                    log_e.set_footer(text=now_ts())
                    await send_log(log_e)
                else:
                    self._build_buttons()
                    await interaction.edit_original_response(embed=self.game_embed("playing"), view=self)

    async def _cashout(self, interaction: discord.Interaction):
        async with self._lock:
            if self.done:
                await interaction.response.send_message("Game already over.", ephemeral=True)
                return
            if self.gems_found == 0:
                await interaction.response.send_message("Find a gem first!", ephemeral=True)
                return
            if self.current_mult <= 1.0:
                await interaction.response.send_message(
                    f"❌ Multiplier is **{self.current_mult:.2f}x** — keep going until it's above **1.00x**!",
                    ephemeral=True)
                return
            self.done = True
            self.stop()
            payout = min(self.current_winnings, MAX_PAYOUT)
            net    = payout - self.bet
            await interaction.response.defer()
            conn = await get_conn()
            try:
                payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "mines")
                await record_game(conn, self.creator.id, True, self.bet, payout, game="mines")
                await log_transaction(conn, self.creator.id, "mines_cashout", net)
                await conn.execute(
                    """INSERT INTO user_stats (user_id, mines_cashouts) VALUES ($1, 1)
                       ON CONFLICT (user_id) DO UPDATE SET mines_cashouts = user_stats.mines_cashouts + 1""",
                    str(self.creator.id)
                )
                if interaction.guild:
                    row = await get_user(conn, self.creator.id)
                    member = interaction.guild.get_member(self.creator.id)
                    if row and member:
                        await update_user_rank(member, row["wagered"])
                    asyncio.create_task(check_vip_balance(interaction.user.id if hasattr(interaction, 'user') else self.creator.id, interaction.guild if hasattr(interaction, 'guild') else None))
            finally:
                await release_conn(conn)
            try:
                await interaction.edit_original_response(embed=self.game_embed("win"), view=None)
            except Exception as _result_err:
                print(f'[RESULT DISPLAY FAILED] {type(_result_err).__name__}: {_result_err}')
            log_e = discord.Embed(title="💣 Mines Result", color=C_WIN)
            log_e.add_field(name="Player",     value=self.creator.mention,        inline=True)
            log_e.add_field(name="Bet",        value=format_amount(self.bet),     inline=True)
            log_e.add_field(name="Mines",      value=str(self.mines),             inline=True)
            log_e.add_field(name="Multiplier", value=f"{self.current_mult:.2f}x", inline=True)
            log_e.add_field(name="Payout",     value=format_amount(payout),       inline=True)
            log_e.add_field(name="Gems Found", value=str(self.gems_found),        inline=True)
            log_e.add_field(name="Outcome",    value="✅ CASHOUT",                inline=True)
            log_e.set_footer(text=now_ts())
            await send_log(log_e)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.done:
            conn = await get_conn()
            try:
                if self.gems_found > 0:
                    payout = min(self.current_winnings, MAX_PAYOUT)
                    payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "mines")
                    await record_game(conn, self.creator.id, True, self.bet, payout, game="mines")
                    await log_transaction(conn, self.creator.id, "mines_timeout_cashout", payout - self.bet)
                    await conn.execute(
                        """INSERT INTO user_stats (user_id, mines_cashouts) VALUES ($1, 1)
                           ON CONFLICT (user_id) DO UPDATE SET mines_cashouts = user_stats.mines_cashouts + 1""",
                        str(self.creator.id)
                    )
                    desc = f"Game timed out — auto cashed out **{format_amount(payout)} 💎** ({self.gems_found} gems found)."
                else:
                    await update_balance(conn, self.creator.id, self.bet)
                    desc = f"Game timed out — bet of **{format_amount(self.bet)}** refunded."
            finally:
                await release_conn(conn)
            try:
                await self._original_message.edit(
                    embed=discord.Embed(color=C_DARK, description=f"## 💣  MINES — EXPIRED\n> {desc}"),
                    view=None)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
        await super().on_timeout()
@bot.tree.command(name="mines", description="Play Mines — find gems and avoid bombs!")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M", mines="Number of mines (1-24)")
async def cmd_mines(interaction: discord.Interaction, bet: str, mines: int):
    wait = check_cooldown("mines", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(f"⏳ Wait **{wait:.1f}s**.", ephemeral=True)
        return
    if is_game_locked("mines", interaction.user):
        await interaction.response.send_message(
            "🔒 **Mines** is currently locked to staff only.", ephemeral=True
        )
        return
    if mines < 1 or mines > 24:
        await interaction.response.send_message("❌ Mines must be between **1** and **24**.", ephemeral=True)
        return
    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return
    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.", ephemeral=True)
                return
        finally:
            await release_conn(conn)
    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view = MinesView(interaction.user, amt, mines)
    view.bet_deducted = True
    await interaction.response.send_message(embed=view.game_embed(), view=view)
    view._original_message = await interaction.original_response()

SCRATCH_SYMBOLS = [
    ("🍒", 1.5,  40),   # Cherry   — very common
    ("🔔", 2.5,  25),   # Bell     — common
    ("⭐", 4.0,  15),   # Star     — uncommon
    ("💎", 7.0,   8),   # Diamond  — rare
    ("7️⃣", 15.0,  4),   # Seven    — very rare
    ("👑", 30.0,  1),   # Crown    — ultra rare
]

SCRATCH_EMOJIS   = [s[0] for s in SCRATCH_SYMBOLS]
SCRATCH_PAYOUTS  = {s[0]: s[1] for s in SCRATCH_SYMBOLS}
SCRATCH_WEIGHTS  = [s[2] for s in SCRATCH_SYMBOLS]

def scratch_generate(force_win: bool = False, force_lose: bool = False) -> list:
    """
    Generate 9 tiles. Win is predetermined with ~35% win rate.
    If win: pick a symbol weighted by rarity, fill 3 matching tiles,
    remaining 6 are random non-matching.
    If loss: ensure no 3 tiles match.
    """
    if force_win:        win = True
    elif force_lose:     win = False
    else:                win = random.random() < 0.2448  # 24.48% win rate → 6% edge

    if win:
        winner = random.choices(SCRATCH_EMOJIS, weights=SCRATCH_WEIGHTS, k=1)[0]
        positions = random.sample(range(9), 3)
        tiles = [None] * 9
        for p in positions:
            tiles[p] = winner
        fillers = [s for s in SCRATCH_EMOJIS if s != winner]
        for i in range(9):
            if tiles[i] is None:
                tiles[i] = random.choices(fillers, k=1)[0]
        from collections import Counter
        counts = Counter(tiles)
        if counts.most_common(1)[0][1] >= 3 and counts.most_common(1)[0][0] != winner:
            return scratch_generate()
        return tiles
    else:
        from collections import Counter
        for _ in range(100):
            tiles = random.choices(SCRATCH_EMOJIS, weights=SCRATCH_WEIGHTS, k=9)
            counts = Counter(tiles)
            if counts.most_common(1)[0][1] < 3:
                return tiles
        tiles = []
        symbols = SCRATCH_EMOJIS.copy()
        for i in range(9):
            available = [s for s in symbols if tiles.count(s) < 2]
            tiles.append(random.choices(available, k=1)[0])
        return tiles

def scratch_check_win(tiles: list):
    """Return (won, symbol, payout_mult) or (False, None, 0)."""
    from collections import Counter
    counts = Counter(tiles)
    for symbol, count in counts.items():
        if count >= 3:
            return True, symbol, SCRATCH_PAYOUTS[symbol]
    return False, None, 0.0

class ScratchView(BaseGameView):
    def __init__(self, creator: discord.User, bet: int):
        super().__init__(timeout=120)
        self.creator      = creator
        self.bet          = bet
        _sc_forced = _force_result.pop(creator.id, None)
        self.tiles        = scratch_generate(
            force_win=(_sc_forced == "win"),
            force_lose=(_sc_forced == "lose")
        )
        self.revealed     = set()
        self.done         = False
        self.bet_deducted = False
        self._lock        = asyncio.Lock()
        self._original_message = None
        self._build_buttons()

    def _build_buttons(self):
        self.clear_items()
        for i in range(9):
            row_num     = i // 3
            is_revealed = i in self.revealed
            btn = discord.ui.Button(
                label=self.tiles[i] if is_revealed else "🎟️",
                style=discord.ButtonStyle.success if is_revealed else discord.ButtonStyle.secondary,
                custom_id=f"scratch_{i}",
                row=row_num,
                disabled=is_revealed or self.done
            )
            if not is_revealed and not self.done:
                btn.callback = self._make_callback(i)
            self.add_item(btn)

        reveal_btn = discord.ui.Button(
            label="🎰 Reveal All",
            style=discord.ButtonStyle.primary,
            custom_id="scratch_reveal_all",
            row=3,
            disabled=self.done
        )
        reveal_btn.callback = self._reveal_all_callback
        self.add_item(reveal_btn)

    def _make_callback(self, index: int):
        async def callback(interaction: discord.Interaction):
            if interaction.user.id != self.creator.id:
                await interaction.response.send_message("❌ Not your card.", ephemeral=True)
                return
            await self._scratch(interaction, index)
        return callback

    async def _reveal_all_callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your card.", ephemeral=True)
            return
        async with self._lock:
            if self.done:
                await interaction.response.send_message("❌ Already done.", ephemeral=True)
                return

        await interaction.response.defer()

        async with self._lock:
            if not await self._deduct_bet():
                await interaction.followup.send("❌ Insufficient balance.", ephemeral=True)
                self.done = True
                self.stop()
                return
            for i in range(9):
                self.revealed.add(i)
            await self._finish(interaction)

    def game_embed(self, outcome: str = "playing") -> discord.Embed:
        won, symbol, mult = scratch_check_win(self.tiles)
        revealed_count = len(self.revealed)

        if outcome == "playing":
            color = C_BLUE
            title = "🎫  SCRATCH"
        elif outcome == "win":
            color = C_WIN
            title = "🎫  SCRATCH — WINNER"
        else:
            color = C_LOSS
            title = "🎫  SCRATCH — NO MATCH"

        grid_rows = []
        for r in range(3):
            row_str = ""
            for c in range(3):
                idx = r * 3 + c
                row_str += (self.tiles[idx] + " ") if idx in self.revealed else "🎟️ "
            grid_rows.append(row_str.strip())
        grid_str = "\
".join(grid_rows)

        if outcome == "playing":
            payout = min(int(self.bet * mult), MAX_PAYOUT) if won and revealed_count == 9 else 0
            desc = (
                f"{grid_str}\
\
"
                f"┌─────────────────────────┐\
"
                f"│ 💰 **Bet** • {format_amount(self.bet)} 💎\
"
                f"│ 🎟️ **Scratched** • {revealed_count}/9\
"
                f"└─────────────────────────┘\
"
                f"💡 *Click tiles or use Reveal All*"
            )
        elif outcome == "win":
            payout = min(int(self.bet * mult), MAX_PAYOUT)
            profit = payout - self.bet
            desc = (
                f"{grid_str}\
\
"
                f"┌─────────────────────────┐\
"
                f"│ 🏆 **Match!** {symbol} x3\
"
                f"│ 💰 **Bet** • {format_amount(self.bet)} 💎\
"
                f"│ 📊 **Multiplier** • {mult}x\
"
                f"│ 💵 **Payout** • {format_amount(payout)} 💎\
"
                f"│ ✨ **Profit** • +{format_amount(profit)} 💎\
"
                f"└─────────────────────────┘"
            )
        else:
            desc = (
                f"{grid_str}\
\
"
                f"┌─────────────────────────┐\
"
                f"│ 💰 **Bet** • {format_amount(self.bet)} 💎\
"
                f"│ ❌ **No matching symbols**\
"
                f"└─────────────────────────┘"
            )

        embed = discord.Embed(title=title, description=desc, color=color)
        embed.set_footer(text=f"🎟️ Scratch Card • Match 3 to win!")
        return embed

    async def _deduct_bet(self) -> bool:
        if self.bet_deducted:
            return True
        self.bet_deducted = True
        async with get_user_lock(self.creator.id):
            conn = await get_conn()
            try:
                return await deduct_balance_safe(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)

    async def _scratch(self, interaction: discord.Interaction, index: int):
        async with self._lock:
            if self.done or index in self.revealed:
                await interaction.response.send_message("❌ Already revealed.", ephemeral=True)
                return

        await interaction.response.defer()

        async with self._lock:
            if not await self._deduct_bet():
                await interaction.followup.send("❌ Insufficient balance.", ephemeral=True)
                self.done = True
                self.stop()
                return
            self.revealed.add(index)

            if len(self.revealed) == 9:
                await self._finish(interaction)
            else:
                self._build_buttons()
                await interaction.edit_original_response(
                    embed=self.game_embed("playing"), view=self)

    async def _finish(self, interaction: discord.Interaction):
        """Called when all 9 tiles are revealed."""
        for i in range(9):
            self.revealed.add(i)
        self.done = True
        self.stop()

        won, symbol, mult = scratch_check_win(self.tiles)
        payout = min(int(self.bet * mult), MAX_PAYOUT) if won else 0
        net    = payout - self.bet
        outcome = "win" if won else "loss"

        self._build_buttons()

        try:
            conn = await get_conn()
            try:
                if payout > 0:
                    payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "scratch")
                await record_game(conn, self.creator.id, won, self.bet, payout, "scratch")
                await log_transaction(conn, self.creator.id, "scratch", net)
                await conn.execute(
                    """INSERT INTO user_stats (user_id, scratch_wins) VALUES ($1, 1)
                       ON CONFLICT (user_id) DO UPDATE SET scratch_wins = user_stats.scratch_wins + 1""",
                    str(self.creator.id)
                )
                if interaction.guild:
                    row = await get_user(conn, self.creator.id)
                    member = interaction.guild.get_member(self.creator.id)
                    if row and member:
                        await update_user_rank(member, row["wagered"])
            finally:
                await release_conn(conn)
        except Exception as _db_err:
            print(f"[SCRATCH DB ERROR] {_db_err}")

        print(f'[RESULT ATTEMPT] {self.__class__.__name__} sending result embed')
        try:
            await interaction.edit_original_response(
                embed=self.game_embed(outcome), view=None)
        except Exception as _result_err:
            print(f'[RESULT DISPLAY FAILED] {type(_result_err).__name__}: {_result_err}')

        color = C_WIN if won else C_LOSS
        log_e = discord.Embed(title="🎟️ Scratch Card Result", color=color)
        log_e.add_field(name="Player",  value=self.creator.mention,    inline=True)
        log_e.add_field(name="Bet",     value=format_amount(self.bet), inline=True)
        log_e.add_field(name="Payout",  value=format_amount(payout),   inline=True)
        log_e.add_field(name="Outcome", value=f"{'🏆 WIN' if won else '❌ LOSS'} {f'({symbol} x{mult})' if won else ''}", inline=True)
        log_e.set_footer(text=now_ts())
        await send_log(log_e)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.done:
            if True:  # bet always deducted upfront now
                conn = await get_conn()
                try:
                    await update_balance(conn, self.creator.id, self.bet)
                finally:
                    await release_conn(conn)
                desc = f"Game timed out — bet of **{format_amount(self.bet)}** refunded."
            else:
                desc = "Game timed out. No bet was taken."
            try:
                await self._original_message.edit(
                    embed=discord.Embed(color=C_DARK, description=f"## 🎫  SCRATCH — EXPIRED\n> {desc}"),
                    view=None)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
        await super().on_timeout()
        await super().on_timeout()

@bot.tree.command(name="scratch", description="Scratch and match 3 symbols to win big!")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M")
async def cmd_scratch(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("scratch", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(
            f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("scratch", interaction.user):
        await interaction.response.send_message(
            "🔒 **Scratch** is currently locked to staff only.", ephemeral=True
        )
        return
    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return
    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)
    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view = ScratchView(interaction.user, amt)
    view.bet_deducted = True
    await interaction.response.send_message(embed=view.game_embed(), view=view)
    view._original_message = await interaction.original_response()

HORSE_NAMES  = ["Thunder", "Blaze", "Shadow", "Storm"]
HORSE_EMOJIS = ["🟥", "🟦", "🟩", "🟨"]
HORSE_ICONS  = ["🐎", "🐎", "🐎", "🐎"]
TRACK_LENGTH = 12  # positions to finish line
TICK_DELAY   = 0.9  # seconds between animation ticks
HORSE_PAYOUT = 3.76  # 4 horses equal odds, 6% edge: fair=4x, house cut=3.76x

def hr_render(positions: list, finished: list = None) -> str:
    """Render the race track as a string."""
    lines = []
    lines.append(f"{'─'*28}🏁")
    for i, (name, emoji, pos) in enumerate(zip(HORSE_NAMES, HORSE_EMOJIS, positions)):
        done = finished and i in finished
        track = ["▪️"] * TRACK_LENGTH
        track_str = ""
        for t in range(TRACK_LENGTH):
            if t < pos:
                track_str += "  "
            elif t == min(pos, TRACK_LENGTH - 1):
                track_str += "🐎"
            else:
                track_str += "▪️"
        medal = ""
        if finished:
            if   finished.index(i) == 0 if i in finished else None: medal = " 🥇"
            rank = finished.index(i) + 1 if i in finished else ""
            medal = f" #{rank}" if i in finished else ""
        lines.append(f"{emoji}`{name:<7}` {track_str}{medal}")
    lines.append(f"{'─'*28}🏁")
    return "\
".join(lines)

def hr_race_embed(positions: list, bet: int, chosen: int,
                  finished: list = None, done: bool = False,
                  won: bool = False) -> discord.Embed:
    horse_name = HORSE_NAMES[chosen]
    emoji      = HORSE_EMOJIS[chosen]

    if not done:
        color = C_GOLD
        title = "🏇  HORSE RACE"
    elif won:
        color = C_WIN
        title = "🏇  HORSE RACE — YOUR HORSE WON"
    else:
        winner_idx = finished[0] if finished else 0
        color = C_LOSS
        title = f"🏇  HORSE RACE — {HORSE_NAMES[winner_idx].upper()} WINS"

    payout = min(int(bet * HORSE_PAYOUT), MAX_PAYOUT) if won else 0
    profit = payout - bet

    track = hr_render(positions, finished if done else None)

    stats = (
        f"┌─────────────────────────┐\
"
        f"│ 🐎 **Your Horse** • {emoji} {horse_name}\
"
        f"│ 💰 **Bet** • {format_amount(bet)} 💎\
"
    )
    if done:
        if won:
            stats += (
                f"│ 📊 **Multiplier** • {HORSE_PAYOUT}x\
"
                f"│ 💵 **Payout** • {format_amount(payout)} 💎\
"
                f"│ ✨ **Profit** • +{format_amount(profit)} 💎\
"
            )
        else:
            stats += f"│ ❌ **Result** • Better luck next time!\
"
    else:
        stats += f"│ 🎯 **Payout if win** • {format_amount(int(bet*HORSE_PAYOUT))} 💎\
"
    stats += f"└─────────────────────────┘"

    embed = discord.Embed(
        title=title,
        description=f"{stats}\
\
{track}",
        color=color
    )
    embed.set_footer(text=f"🏇 Horse Race • {'Race Over!' if done else 'Racing...'}")
    return embed

@bot.tree.command(name="horserace", description="Back a horse — pick right and win 3.8×!")
@app_commands.describe(
    bet="Bet amount e.g. 5k, 1M",
    horse="Horse number (1-4)"
)
async def cmd_horserace(interaction: discord.Interaction, bet: str, horse: int):
    wait = check_cooldown("horserace", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(
            f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("horserace", interaction.user):
        await interaction.response.send_message(
            "🔒 **Horse Race** is currently locked to staff only.", ephemeral=True
        )
        return

    if horse < 1 or horse > 4:
        await interaction.response.send_message(
            "❌ Choose a horse between **1** and **4**.", ephemeral=True)
        return

    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            row = await get_user(conn, interaction.user.id)
            if not row or row["balance"] < amt:
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                await interaction.response.send_message("❌ Insufficient balance.", ephemeral=True)
                return
        finally:
            await release_conn(conn)

    chosen = horse - 1  # 0-indexed

    _hr_forced = _force_result.pop(interaction.user.id, None)
    if _hr_forced == "win":    winner_idx = chosen  # force player's horse to win
    elif _hr_forced == "lose": winner_idx = (chosen + 1) % 4  # force a different horse
    else:                       winner_idx = random.randint(0, 3)

    positions = [0, 0, 0, 0]
    finished  = []  # order of finish

    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    await interaction.response.send_message(
        embed=hr_race_embed(positions, amt, chosen))
    msg = await interaction.original_response()

    max_ticks = 40
    for tick in range(max_ticks):
        for i in range(4):
            if i in finished:
                continue

            remaining = len([x for x in range(4) if x not in finished])
            ticks_left = max_ticks - tick

            if i == winner_idx and ticks_left < 8 and i not in finished:
                step = random.choices([1, 2], weights=[1, 3])[0]
            elif i != winner_idx and positions[winner_idx] > TRACK_LENGTH - 3:
                step = random.choices([0, 1], weights=[2, 1])[0]
            else:
                step = random.choices([0, 1, 2], weights=[2, 5, 3])[0]

            positions[i] = min(positions[i] + step, TRACK_LENGTH)

            if positions[i] >= TRACK_LENGTH and i not in finished:
                finished.append(i)

        done = len(finished) == 4 or (finished and tick > 5)

        try:
            await msg.edit(embed=hr_race_embed(
                positions, amt, chosen,
                finished=finished if done else None,
                done=done,
                won=(finished[0] == chosen) if finished else False
            ))
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass

        if done:
            break

        await asyncio.sleep(TICK_DELAY)

    if not finished:
        finished = list(range(4))
        random.shuffle(finished)
    if winner_idx in finished:
        finished.remove(winner_idx)
    finished.insert(0, winner_idx)

    won = finished[0] == chosen
    payout = min(int(amt * HORSE_PAYOUT), MAX_PAYOUT) if won else 0

    try:
        await msg.edit(embed=hr_race_embed(
            positions, amt, chosen,
            finished=finished, done=True, won=won))
    except Exception as _err:
        print(f"[ERROR] Failed to send error message: {_err}")
        pass

    conn = await get_conn()
    try:
        if payout > 0:
            payout = await apply_win_payout(conn, interaction.user.id, payout, amt, "horserace")
        else:
            pass  # bet already deducted, loss is correct
        await record_game(conn, interaction.user.id, won, amt, payout, "horserace")
        await log_transaction(conn, interaction.user.id, "horserace", payout - amt)
        if interaction.guild:
            row = await get_user(conn, interaction.user.id)
            member = interaction.guild.get_member(interaction.user.id)
            if row and member:
                await update_user_rank(member, row["wagered"])
    except Exception as e:
        print(f"[HORSERACE] DB error, refunding bet: {e}")
        try:
            await update_balance(conn, interaction.user.id, amt)
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass
    finally:
        await release_conn(conn)

    log_e = discord.Embed(title="🏇 Horse Race Result",
                          color=C_WIN if won else C_LOSS)
    log_e.add_field(name="Player",  value=interaction.user.mention,              inline=True)
    log_e.add_field(name="Bet",     value=format_amount(amt),                    inline=True)
    log_e.add_field(name="Horse",   value=f"{HORSE_EMOJIS[chosen]} {HORSE_NAMES[chosen]}", inline=True)
    log_e.add_field(name="Winner",  value=f"{HORSE_EMOJIS[finished[0]]} {HORSE_NAMES[finished[0]]}", inline=True)
    log_e.add_field(name="Payout",  value=format_amount(payout),                 inline=True)
    log_e.add_field(name="Outcome", value="✅ WIN" if won else "❌ LOSS",         inline=True)
    log_e.set_footer(text=now_ts())
    await send_log(log_e)
    _end_game_session(interaction.user.id)

BALLOON_POP_CHANCES = [
    0.24,  # pump 1  — EV 0.95x at cashout (5% edge)
    0.33,  # pump 2
    0.43,  # pump 3
    0.53,  # pump 4
    0.63,  # pump 5
    0.74,  # pump 6
    0.85,  # pump 7
    0.93,  # pump 8
    0.98,  # pump 9+
]

BALLOON_SIZES = ["🔵", "🔵", "🟣", "🟣", "🟠", "🟠", "🔴", "🔴", "💢", "💥"]

def balloon_pop_chance(pumps: int) -> float:
    idx = min(pumps - 1, len(BALLOON_POP_CHANCES) - 1)
    return BALLOON_POP_CHANCES[idx]

def balloon_mult(pumps: int) -> float:
    return round(1.0 + pumps * 0.25, 2)

def balloon_render(pumps: int, popped: bool = False, pumping: bool = False) -> str:
    if popped:
        frames = [
            "      💥      ",
            "    💥   💥    ",
            "  💥   💥   💥  ",
        ]
        return "\
".join(frames)

    if pumping:
        size_idx = min(pumps, len(BALLOON_SIZES) - 1)
        balloon = BALLOON_SIZES[size_idx]
        lines = [
            f"",
            f"    {balloon}{balloon}{balloon}    ",
            f"  {balloon}{balloon}{balloon}{balloon}{balloon}  ",
            f"    {balloon}{balloon}{balloon}    ",
            f"      |      ",
            f"      |      ",
        ]
        return "\
".join(lines)

    size_idx = min(pumps, len(BALLOON_SIZES) - 1)
    balloon = BALLOON_SIZES[size_idx]

    if pumps == 0:
        lines = [
            f"",
            f"     {balloon}     ",
            f"    {balloon}{balloon}    ",
            f"     {balloon}     ",
            f"      |      ",
            f"      |      ",
        ]
    elif pumps <= 2:
        lines = [
            f"    {balloon}{balloon}    ",
            f"  {balloon}{balloon}{balloon}{balloon}  ",
            f"    {balloon}{balloon}    ",
            f"      |      ",
            f"      |      ",
        ]
    elif pumps <= 4:
        lines = [
            f"   {balloon}{balloon}{balloon}   ",
            f" {balloon}{balloon}{balloon}{balloon}{balloon} ",
            f"{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}",
            f" {balloon}{balloon}{balloon}{balloon}{balloon} ",
            f"   {balloon}{balloon}{balloon}   ",
            f"      |      ",
        ]
    elif pumps <= 6:
        lines = [
            f"  {balloon}{balloon}{balloon}{balloon}  ",
            f"{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}",
            f"{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}",
            f"{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}",
            f"  {balloon}{balloon}{balloon}{balloon}  ",
            f"      |      ",
        ]
    else:
        lines = [
            f" {balloon}{balloon}{balloon}{balloon}{balloon} ",
            f"{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}",
            f"{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}",
            f"{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}",
            f"{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}{balloon}",
            f" {balloon}{balloon}{balloon}{balloon}{balloon} ",
            f"      |      ",
        ]
    return "\
".join(lines)

class BalloonView(BaseGameView):
    def __init__(self, creator: discord.User, bet: int):
        super().__init__(timeout=180)
        self.creator      = creator
        self.bet          = bet
        self.pumps        = 0
        self.done         = False
        self.bet_deducted = False
        self._lock        = asyncio.Lock()
        self._original_message = None
        self._update_buttons()

    def _update_buttons(self):
        self.pump_btn.disabled    = self.done
        self.cashout_btn.disabled = self.done or self.pumps == 0

    def game_embed(self, outcome: str = "playing", pumping: bool = False) -> discord.Embed:
        mult   = balloon_mult(self.pumps)
        payout = min(int(self.bet * mult), MAX_PAYOUT)
        profit = payout - self.bet
        next_pop = balloon_pop_chance(self.pumps + 1) * 100

        if outcome == "playing":
            color = C_BLUE
            title = "🎈  PUMP THE BALLOON"
        elif outcome == "pumping":
            color = C_GOLD
            title = "🎈 Pumping..."
        elif outcome == "win":
            color = C_WIN
            title = "💰 Cashed Out!"
        else:
            color = C_LOSS
            title = "💥  POP — BALLOON BURST"

        balloon_art = balloon_render(
            self.pumps,
            popped=(outcome == "loss"),
            pumping=pumping
        )

        if outcome in ("win", "loss"):
            stats = (
                f"┌─────────────────────────┐\
"
                f"│ 🎈 **Pumps** • {self.pumps}\
"
                f"│ 💰 **Bet** • {format_amount(self.bet)} 💎\
"
                f"│ 📊 **Multiplier** • {mult:.2f}x\
"
            )
            if outcome == "win":
                stats += (
                    f"│ 💵 **Payout** • {format_amount(payout)} 💎\
"
                    f"│ ✨ **Profit** • +{format_amount(profit)} 💎\
"
                )
            else:
                stats += f"│ ❌ **Lost** • {format_amount(self.bet)} 💎\
"
            stats += "└─────────────────────────┘"
        else:
            stats = (
                f"┌─────────────────────────┐\
"
                f"│ 🎈 **Pumps** • {self.pumps}\
"
                f"│ 💰 **Bet** • {format_amount(self.bet)} 💎\
"
                f"│ 📊 **Multiplier** • {mult:.2f}x\
"
                f"│ 💵 **Payout** • {format_amount(payout)} 💎\
"
                f"│ 💀 **Next pop risk** • {next_pop:.0f}%\
"
                f"└─────────────────────────┘"
            )
            if self.pumps == 0:
                stats += "\
💡 *Pump at least once before cashing out!*"
            else:
                stats += "\
💡 *Click 💎 Cashout to lock in your profit!*"

        embed = discord.Embed(
            title=title,
            description=f"```\
{balloon_art}\
```\
{stats}",
            color=color
        )
        embed.set_footer(text=f"🎈 Balloon Game • {'Game Over' if outcome in ('win','loss') else f'Pump #{self.pumps+1} next'}")
        return embed

    async def _deduct_bet(self) -> bool:
        if self.bet_deducted:
            return True
        self.bet_deducted = True
        async with get_user_lock(self.creator.id):
            conn = await get_conn()
            try:
                return await deduct_balance_safe(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)

    @discord.ui.button(label="🎈 Pump", style=discord.ButtonStyle.primary)
    async def pump_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your balloon.", ephemeral=True)
            return
        async with self._lock:
            if self.done:
                await interaction.response.send_message("❌ Game over.", ephemeral=True)
                return

        await interaction.response.defer()

        async with self._lock:
            if not await self._deduct_bet():
                await interaction.followup.send(
                    "❌ Insufficient balance. Game cancelled.", ephemeral=True)
                self.done = True
                self.stop()
                return

            self._update_buttons()
            await interaction.edit_original_response(
                embed=self.game_embed("pumping", pumping=True), view=self)
            await asyncio.sleep(0.8)

            pop_chance = balloon_pop_chance(self.pumps + 1)
            _pb_forced = _force_result.get(self.creator.id)  # peek, don't pop yet
            if _pb_forced == "lose":
                _force_result.pop(self.creator.id, None)
                popped = True
            elif _pb_forced == "win":
                popped = False   # never pop while forced win active
            else:
                popped = random.random() < BOT_HOUSE_WIN

            self.pumps += 1

            if popped:
                self.done = True
                self.stop()
                self._update_buttons()

                conn = await get_conn()
                try:
                    await record_game(conn, self.creator.id, False, self.bet, 0, game="balloon")
                    await conn.execute(
                        """INSERT INTO user_stats (user_id, balloon_pops) VALUES ($1, 1)
                           ON CONFLICT (user_id) DO UPDATE SET balloon_pops = user_stats.balloon_pops + 1""",
                        str(self.creator.id)
                    )
                    await log_transaction(conn, self.creator.id, "balloon_pop", -self.bet)
                    _rank_guild = interaction.guild or bot.get_guild(GUILD_ID)
                    if _rank_guild:
                        row = await get_user(conn, self.creator.id)
                        member = _rank_guild.get_member(self.creator.id)
                        if row and member:
                            await update_user_rank(member, row["wagered"])
                finally:
                    await release_conn(conn)

                try:
                    await interaction.edit_original_response(
                        embed=self.game_embed("loss"), view=None)
                except Exception as _result_err:
                    print(f'[RESULT DISPLAY FAILED] {type(_result_err).__name__}: {_result_err}')

                log_e = discord.Embed(title="🎈 Balloon Result", color=C_LOSS)
                log_e.add_field(name="Player",  value=self.creator.mention,    inline=True)
                log_e.add_field(name="Bet",     value=format_amount(self.bet), inline=True)
                log_e.add_field(name="Pumps",   value=str(self.pumps),         inline=True)
                log_e.add_field(name="Outcome", value="💥 POPPED",             inline=True)
                log_e.set_footer(text=now_ts())
                await send_log(log_e)

            else:
                self._update_buttons()
                await interaction.edit_original_response(
                    embed=self.game_embed("playing"), view=self)

    @discord.ui.button(label="💎 Cashout", style=discord.ButtonStyle.green)
    async def cashout_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your balloon.", ephemeral=True)
            return
        async with self._lock:
            if self.done:
                await interaction.response.send_message("❌ Game over.", ephemeral=True)
                return
            if self.pumps == 0:
                await interaction.response.send_message(
                    "❌ Pump at least once before cashing out!", ephemeral=True)
                return
            self.done = True
            self.stop()
            self._update_buttons()

        await interaction.response.defer()

        async with self._lock:
            _force_result.pop(self.creator.id, None)

            payout = min(int(self.bet * balloon_mult(self.pumps)), MAX_PAYOUT)
            net    = payout - self.bet

            conn = await get_conn()
            try:
                payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "balloon")
                await record_game(conn, self.creator.id, True, self.bet, payout, game="balloon")

                await conn.execute(
                    """INSERT INTO user_stats (user_id, balloon_cashouts) VALUES ($1, 1)
                       ON CONFLICT (user_id) DO UPDATE SET balloon_cashouts = user_stats.balloon_cashouts + 1""",
                    str(self.creator.id)
                )
                await log_transaction(conn, self.creator.id, "balloon_cashout", net)
                if interaction.guild:
                    row = await get_user(conn, self.creator.id)
                    member = interaction.guild.get_member(self.creator.id)
                    if row and member:
                        await update_user_rank(member, row["wagered"])
                    asyncio.create_task(check_vip_balance(interaction.user.id if hasattr(interaction, 'user') else self.creator.id, interaction.guild if hasattr(interaction, 'guild') else None))
            finally:
                await release_conn(conn)

            try:
                await interaction.edit_original_response(
                    embed=self.game_embed("win"), view=None)
            except Exception as _result_err:
                print(f'[RESULT DISPLAY FAILED] {type(_result_err).__name__}: {_result_err}')

            log_e = discord.Embed(title="🎈 Balloon Result", color=C_WIN)
            log_e.add_field(name="Player",     value=self.creator.mention,                 inline=True)
            log_e.add_field(name="Bet",        value=format_amount(self.bet),              inline=True)
            log_e.add_field(name="Pumps",      value=str(self.pumps),                      inline=True)
            log_e.add_field(name="Multiplier", value=f"{balloon_mult(self.pumps):.2f}x",   inline=True)
            log_e.add_field(name="Payout",     value=format_amount(payout),                inline=True)
            log_e.add_field(name="Outcome",    value="✅ CASHOUT",                         inline=True)
            log_e.set_footer(text=now_ts())
            await send_log(log_e)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.done:
            conn = await get_conn()
            try:
                if self.pumps > 0:
                    payout = min(int(self.bet * balloon_mult(self.pumps)), MAX_PAYOUT)
                    payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "balloon")
                    await record_game(conn, self.creator.id, True, self.bet, payout, game="balloon")
                    await log_transaction(conn, self.creator.id, "balloon_timeout_cashout", payout - self.bet)
                    desc = f"Game timed out — auto cashed out **{format_amount(payout)} 💎** ({self.pumps} pumps)."
                else:
                    await update_balance(conn, self.creator.id, self.bet)
                    desc = f"Game timed out — bet of **{format_amount(self.bet)}** refunded."
            finally:
                await release_conn(conn)
            try:
                await self._original_message.edit(
                    embed=discord.Embed(color=C_DARK, description=f"## 🎈  BALLOON — EXPIRED\n> {desc}"),
                    view=None)
            except Exception as e:
                print(f"[ERROR] {type(e).__name__}: {e}")
        await super().on_timeout()

SLOTS_SYMBOLS = [
    ("🍒", 30, 1.5,  0.5),
    ("🍋", 25, 2.0,  0.8),
    ("🍊", 20, 2.5,  1.0),
    ("🍇", 15, 3.5,  1.5),
    ("🍉", 10, 5.0,  2.0),
    ("⭐", 6,  10.0, 3.0),
    ("💎", 3,  20.0, 5.0),
    ("7️⃣", 1,  50.0, 10.0),
]

SLOTS_SPIN_FRAMES = [
    ["🎰","🎰","🎰"],
    ["🍒","🎰","🎰"],
    ["🍋","🍊","🎰"],
    ["🍇","🍉","🎰"],
]

def _slots_roll() -> list:
    """Roll 3 reels — returns list of (emoji, weight, 3x, 2x)."""
    weights = [s[1] for s in SLOTS_SYMBOLS]
    return [random.choices(SLOTS_SYMBOLS, weights=weights, k=1)[0] for _ in range(3)]

def _slots_payout(reels: list, bet: int) -> tuple[int, str, float]:
    """Return (payout, result_label, multiplier)."""
    emojis = [r[0] for r in reels]
    if emojis[0] == emojis[1] == emojis[2]:
        mult = reels[0][2]  # 3x match
        label = f"3x {emojis[0]} — JACKPOT!" if mult >= 10 else f"3x {emojis[0]} — Triple Match!"
        return int(bet * mult), label, mult
    elif emojis[0] == emojis[1] or emojis[1] == emojis[2]:
        sym = reels[1]
        mult = sym[3]  # 2x match
        label = f"2x {sym[0]} — Partial Match"
        return int(bet * mult), label, mult
    return 0, "No Match", 0.0

def _slots_reels_str(reels: list) -> str:
    """Format 3 reels into a display string."""
    return "  ".join(r[0] for r in reels)

def _slots_paytable_str() -> str:
    lines = []
    for emoji, _, m3, m2 in SLOTS_SYMBOLS:
        lines.append(f"{emoji} **3x:** `{m3}x`  **2x:** `{m2}x`")
    return "\n".join(lines)

class SlotsView(BaseGameView):
    def __init__(self, creator: discord.Member, bet: int):
        super().__init__(timeout=60)
        self.creator        = creator
        self.bet            = bet
        self._original_message = None
        self._spinning      = False

    def _ready_embed(self) -> discord.Embed:
        e = discord.Embed(
            color=C_GOLD,
            description=(
                f"## 🎰  SLOT MACHINE\n"
                f"```\n  wager   {format_amount(self.bet):>14}\n```\n"
                f"{_slots_paytable_str()}\n"
            )
        )
        _brand_embed(e)
        return e

    @discord.ui.button(label="🎰  SPIN!", style=discord.ButtonStyle.danger, custom_id="slots_spin")
    async def spin_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ This isn't your game.", ephemeral=True)
            return
        if self._spinning:
            await interaction.response.send_message("⏳ Already spinning!", ephemeral=True)
            return
        self._spinning = True
        button.disabled = True

        await interaction.response.defer()

        conn = await get_conn()
        try:
            row = await get_user(conn, self.creator.id)
            if not row or row["balance"] < self.bet:
                await interaction.followup.send("❌ Insufficient balance.", ephemeral=True)
                self._spinning = False
                button.disabled = False
                await self._original_message.edit(view=self)
                return
            await conn.execute(
                "UPDATE users SET balance = balance - $1 WHERE user_id = $2",
                self.bet, str(self.creator.id)
            )
        finally:
            await release_conn(conn)

        reels = _slots_roll()

        forced = _force_result.pop(self.creator.id, None)
        if forced == "win":
            best = max(SLOTS_SYMBOLS, key=lambda s: s[2])
            reels = [best, best, best]
        elif forced == "lose":
            reels = [SLOTS_SYMBOLS[0], SLOTS_SYMBOLS[1], SLOTS_SYMBOLS[2]]

        payout, result_label, mult = _slots_payout(reels, self.bet)
        won = payout > 0

        spin_frames = [
            ["❓", "❓", "❓"],
            [reels[0][0], "❓", "❓"],
            [reels[0][0], reels[1][0], "❓"],
        ]
        for frame in spin_frames:
            spinning_embed = discord.Embed(
                color=C_GOLD,
                description=(
                    f"## 🎰  SLOTS — SPINNING\n"
                    f"```\n  {'  '.join(frame)}  \n```"
                )
            )
            try:
                await self._original_message.edit(embed=spinning_embed, view=self)
            except Exception:
                pass
            await asyncio.sleep(0.8)

        if won:
            color  = C_WIN
            header = f"🎉  {result_label}"
            net_str = f"+{format_amount(payout - self.bet)} 💎"
        else:
            color  = 0xE74C3C
            header = f"💔  {result_label}"
            net_str = f"-{format_amount(self.bet)} 💎"

        _slot_tag = "+" if won else "-"
        result_embed = discord.Embed(
            color=color,
            description=(
                f"## 🎰  SLOTS  —  {result_label}\n"
                f"```\n  {_slots_reels_str(reels)}  \n```\n"
                f"```diff\n"
                f"{_slot_tag} {net_str}\n"
                f"# {mult}×  ·  wager {format_amount(self.bet)} 💎\n"
                f"```"
            )
        )
        _brand_embed(result_embed)

        self.clear_items()
        again_btn = discord.ui.Button(label="🎰  Spin Again!", style=discord.ButtonStyle.danger)
        async def again_callback(itx: discord.Interaction):
            if itx.user.id != self.creator.id:
                await itx.response.send_message("❌ This isn't your game.", ephemeral=True)
                return
            self._spinning = False
            self.clear_items()
            self.add_item(self.spin_btn)
            self.spin_btn.disabled = False
            await itx.response.edit_message(embed=self._ready_embed(), view=self)
        again_btn.callback = again_callback
        self.add_item(again_btn)

        conn = await get_conn()
        try:
            if won:
                payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "slots")
            await record_game(conn, self.creator.id, won, self.bet, payout, "slots")
            await log_transaction(conn, self.creator.id, "slots", payout - self.bet)
            if interaction.guild:
                row = await get_user(conn, self.creator.id)
                member = interaction.guild.get_member(self.creator.id)
                if row and member:
                    await update_user_rank(member, row["wagered"])
        finally:
            await release_conn(conn)

        _end_game_session(self.creator.id)
        try:
            await self._original_message.edit(embed=result_embed, view=self)
        except Exception as e:
            print(f"[SLOTS] Final edit failed: {e}")

        log_e = discord.Embed(
            title=f"🎰 Slots — {'Win' if won else 'Loss'}",
            color=color
        )
        log_e.add_field(name="Player", value=self.creator.mention, inline=True)
        log_e.add_field(name="Bet",    value=format_amount(self.bet), inline=True)
        log_e.add_field(name="Mult",   value=f"{mult}x",              inline=True)
        log_e.add_field(name="Payout", value=format_amount(payout),   inline=True)
        log_e.add_field(name="Reels",  value=_slots_reels_str(reels), inline=True)
        log_e.set_footer(text=now_ts())
        await send_finance_log(log_e)

@bot.tree.command(name="slots", description="Spin the slot machine — match symbols to win big!")
@app_commands.describe(amount="Amount to bet (e.g. 1K, 500K, 1M)")
async def cmd_slots(interaction: discord.Interaction, amount: str):
    wait = check_cooldown("slots", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(
            f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("slots", interaction.user):
        await interaction.response.send_message(
            "🔒 **Slots** is currently locked to staff only.", ephemeral=True
        )
        return
    amt = parse_amount(amount)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return

    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        row = await get_user(conn, interaction.user.id)
    finally:
        await release_conn(conn)

    if not row or row["balance"] < amt:
        await interaction.response.send_message("❌ Insufficient balance.", ephemeral=True)
        return

    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view = SlotsView(creator=interaction.user, bet=amt)
    await interaction.response.send_message(embed=view._ready_embed(), view=view)
    view._original_message = await interaction.original_response()

@bot.tree.command(name="pumpballoon", description="Pump for +25% each round — don't let it pop!")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M")
async def cmd_pumpballoon(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("pumpballoon", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(
            f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("pumpballoon", interaction.user):
        await interaction.response.send_message(
            "🔒 **Pump Balloon** is currently locked to staff only.", ephemeral=True)
        return
    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return
    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)
    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view = BalloonView(interaction.user, amt)
    view.bet_deducted = True
    await interaction.response.send_message(embed=view.game_embed(), view=view)
    view._original_message = await interaction.original_response()

BOT_HOUSE_WIN_CD = 0.52    # 52/48 edge matching all other games

CD_COLORS = [
    ("🔴", "Red"),
    ("🔵", "Blue"),
    ("🟢", "Green"),
    ("🟡", "Yellow"),
]

CD_DICE_FACES = ["⚀","⚁","⚂","⚃","⚄","⚅"]

def cd_roll_slots() -> list:
    return [random.choice(CD_COLORS) for _ in range(6)]

def cd_count(slots: list, color_name: str) -> int:
    return sum(1 for emoji, name in slots if name == color_name)

def cd_render_spinning(spin_frame: int) -> str:
    faces = [CD_DICE_FACES[(spin_frame + i) % 6] for i in range(6)]
    return "  ".join(faces)

def cd_render_result(slots: list, chosen_name: str) -> str:
    parts = []
    for emoji, name in slots:
        parts.append(f"[{emoji}]" if name == chosen_name else f" {emoji} ")
    return "  ".join(parts)

def cd_game_embed(bet: int, chosen: str = None, slots: list = None,
                  outcome: str = None, spin_frame: int = 0) -> discord.Embed:

    if outcome is None:
        color = C_BLUE
        title = "⚄  COLOR DICE"
        dice_display = "⚀  ⚁  ⚂  ⚃  ⚄  ⚅"
        stats = (
            f"┌─────────────────────────┐\
"
            f"│ 💰 **Bet** • {format_amount(bet)} 💎\
"
            f"│ 🏆 **Win** • 2x if color lands once\
"
            f"│ 🤝 **Tie** • Refund if it lands 2+\
"
            f"│ ❌ **Lose** • If color doesn't appear\
"
            f"└─────────────────────────┘\
"
            f"👇 *Pick your color below!*"
        )
    elif outcome == "spinning":
        color = C_GOLD
        title = "⚄  ROLLING..."
        dice_display = cd_render_spinning(spin_frame)
        chosen_emoji = next(e for e, n in CD_COLORS if n == chosen)
        stats = (
            f"┌─────────────────────────┐\
"
            f"│ 🎯 **Your Pick** • {chosen_emoji} {chosen}\
"
            f"│ 💰 **Bet** • {format_amount(bet)} 💎\
"
            f"│ ⏳ **Rolling...**\
"
            f"└─────────────────────────┘"
        )
    else:
        count = cd_count(slots, chosen)
        chosen_emoji = next(e for e, n in CD_COLORS if n == chosen)
        dice_display = cd_render_result(slots, chosen)
        payout = min(int(bet * 2), MAX_PAYOUT) if outcome == "win" else (bet if outcome == "tie" else 0)
        net = payout - bet

        if outcome == "win":
            color = C_WIN
            title = "⚄  ✦ YOUR COLOR WINS"
            result_line = f"│ ✨ **Profit** • +{format_amount(net)} 💎\
"
        elif outcome == "tie":
            color = C_GOLD
            title = "⚄  ↩ PUSH — REFUNDED"
            result_line = f"│ 🔄 **Refunded** • {format_amount(bet)} 💎\
"
        else:
            color = C_LOSS
            title = "💀 NOT THIS TIME!"
            result_line = f"│ ❌ **Lost** • {format_amount(bet)} 💎\
"

        stats = (
            f"┌─────────────────────────┐\
"
            f"│ 🎯 **Your Pick** • {chosen_emoji} {chosen}\
"
            f"│ 🎲 **Appearances** • {count}x\
"
            f"│ 💰 **Bet** • {format_amount(bet)} 💎\
"
            f"{result_line}"
            f"└─────────────────────────┘"
        )

    embed = discord.Embed(
        title=title,
        description=f"```\
{dice_display}\
```\
{stats}",
        color=color
    )
    embed.set_footer(text="🎲 Color Dice • Land once = win, twice = tie, none = lose")
    return embed

class CDColorButton(discord.ui.Button):
    def __init__(self, emoji: str, name: str):
        super().__init__(
            label=name,
            emoji=emoji,
            style=discord.ButtonStyle.secondary
        )
        self.color_emoji = emoji
        self.color_name  = name

    async def callback(self, interaction: discord.Interaction):
        await self.view._pick(interaction, self.color_emoji, self.color_name)

class ColorDiceView(BaseGameView):
    def __init__(self, creator: discord.User, bet: int):
        super().__init__(timeout=60)
        self.creator  = creator
        self.bet      = bet
        self.chosen   = None
        self.done     = False
        self.used     = False
        self._lock    = asyncio.Lock()
        self._original_message = None
        for emoji, name in CD_COLORS:
            self.add_item(CDColorButton(emoji, name))

    async def _pick(self, interaction: discord.Interaction, chosen_emoji: str, chosen_name: str):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your game.", ephemeral=True)
            return
        async with self._lock:
            if self.done or self.used:
                await interaction.response.send_message("❌ Already rolling!", ephemeral=True)
                return
            self.used   = True
            self.chosen = chosen_name
            self.done   = True
            self.stop()

        await interaction.response.defer()

        async with get_user_lock(self.creator.id):
            conn = await get_conn()
            try:
                deducted = await deduct_balance_safe(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)
        if not deducted:
            await interaction.followup.send(
                f"❌ Insufficient balance. Need **{format_amount(self.bet)}**.", ephemeral=True)
            return
        msg = await interaction.original_response()

        slots = cd_roll_slots()
        count = cd_count(slots, chosen_name)
        if count == 1 and random.random() < BOT_HOUSE_WIN:
            attempts = 0
            while count == 1 and attempts < 50:
                slots = cd_roll_slots()
                count = cd_count(slots, chosen_name)
                attempts += 1

        outcome = "win" if count == 1 else ("tie" if count >= 2 else "loss")
        payout  = int(self.bet * 2) if outcome == "win" else (self.bet if outcome == "tie" else 0)
        net     = payout - self.bet

        for frame in range(12):
            try:
                await msg.edit(
                    embed=cd_game_embed(self.bet, chosen_name, outcome="spinning", spin_frame=frame),
                    view=None)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
            delay = 0.18 if frame < 8 else 0.45
            await asyncio.sleep(delay)

        try:
            await msg.edit(embed=cd_game_embed(self.bet, chosen_name, slots=slots, outcome=outcome), view=None)
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass

        conn = await get_conn()
        try:
            if payout > 0:
                payout = await apply_win_payout(conn, self.creator.id, payout, self.bet, "colordice")
            won = outcome == "win"
            if outcome == "tie":
                await conn.execute(
                    "UPDATE users SET wagered=wagered+$1, last_updated=$2 WHERE user_id=$3",
                    self.bet, now_ts(), str(self.creator.id))
            else:
                await record_game(conn, self.creator.id, won, self.bet, payout, "colordice")
            await log_transaction(conn, self.creator.id, "colordice", net)
            if interaction.guild:
                row = await get_user(conn, self.creator.id)
                member = interaction.guild.get_member(self.creator.id)
                if row and member:
                    await update_user_rank(member, row["wagered"])
        finally:
            await release_conn(conn)

        color_log = C_WIN if outcome == "win" else (C_GOLD if outcome == "tie" else C_LOSS)
        log_e = discord.Embed(title="🎲 Color Dice Result", color=color_log)
        log_e.add_field(name="Player",  value=interaction.user.mention,   inline=True)
        log_e.add_field(name="Bet",     value=format_amount(self.bet),     inline=True)
        log_e.add_field(name="Pick",    value=f"{chosen_emoji} {chosen_name}", inline=True)
        log_e.add_field(name="Count",   value=str(count),                  inline=True)
        log_e.add_field(name="Payout",  value=format_amount(payout),       inline=True)
        log_e.add_field(name="Outcome", value=f"{'🏆 WIN' if outcome=='win' else ('🤝 TIE' if outcome=='tie' else '❌ LOSS')}", inline=True)
        log_e.set_footer(text=now_ts())
        await send_log(log_e)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        if not self.done and not self.used:
            try:
                await self._original_message.edit(
                    embed=discord.Embed(title="🎲  EXPIRED",
                        description="Game timed out — no bet was taken.", color=C_DARK),
                    view=None)
            except Exception as e:
                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
        elif not self.done and self.used:
            conn = await get_conn()
            try:
                await update_balance(conn, self.creator.id, self.bet)
            finally:
                await release_conn(conn)
            try:
                await self._original_message.edit(
                    embed=discord.Embed(title="🎲  EXPIRED",
                        description=f"Game timed out — **{format_amount(self.bet)}** refunded.", color=C_DARK),
                    view=None)
            except Exception as e:
                print(f"[ERROR] {type(e).__name__}: {e}")
        await super().on_timeout()

@bot.tree.command(name="colordice", description="Pick a colour — match once for 2×, twice+ for refund, miss to lose!")
@app_commands.describe(bet="Bet amount e.g. 5k, 1M")
async def cmd_colordice(interaction: discord.Interaction, bet: str):
    wait = check_cooldown("colordice", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(
            f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("colordice", interaction.user):
        await interaction.response.send_message(
            "🔒 **Colordice** is currently locked to staff only.", ephemeral=True
        )
        return
    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return
    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                row = await get_user(conn, interaction.user.id)
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
        finally:
            await release_conn(conn)
    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    view = ColorDiceView(interaction.user, amt)
    view.used = True  # bet already deducted; mark to prevent double deduction
    await interaction.response.send_message(embed=view.game_embed() if False else cd_game_embed(amt), view=view)
    view._original_message = await interaction.original_response()

UPGRADER_MIN_MULT = 1.2
UPGRADER_MAX_MULT = 1000.0

def upgrader_display_chance(mult: float) -> float:
    """What the player sees — looks perfectly fair."""
    return 1.0 / mult

def upgrader_real_chance(mult: float) -> float:
    """Actual win probability — shown * 0.875 (12.5% hidden edge).
    e.g. shown=40% → real=35%.
    """
    return (1.0 / mult) * 0.94  # 6% hidden edge

UPGRADER_WHEEL_SIZE = 40

def upgrader_wheel_render(display_chance: float, arrow_pos: float, outcome: str = "pending") -> str:
    size = UPGRADER_WHEEL_SIZE
    win_segs = max(1, round(display_chance * size))
    wheel = ["🟩"] * win_segs + ["🟥"] * (size - win_segs)

    arrow_idx = int(arrow_pos * size) % size
    window = 15
    half = window // 2
    display = []
    for i in range(window):
        idx = (arrow_idx - half + i) % size
        display.append(wheel[idx])

    arrow_row = " " * (half * 2) + "⬆️"
    wheel_str = "".join(display)

    if outcome == "pending":
        return f"{wheel_str}\n{arrow_row}"
    marker = "✅ WIN ZONE" if outcome == "win" else "❌ LOSE ZONE"
    return f"{wheel_str}\n{arrow_row}\n{marker}"

def upgrader_embed(bet: int, mult: float, outcome: str = "pending", arrow_pos: float = 0.0) -> discord.Embed:
    display_chance = upgrader_display_chance(mult)
    payout = min(int(bet * mult), MAX_PAYOUT)
    profit = payout - bet

    if outcome == "pending":
        color = C_BLUE
        title = "⬆️  UPGRADER"
    elif outcome == "spinning":
        color = C_GOLD
        title = "⬆️  UPGRADER — SPINNING..."
    elif outcome == "win":
        color = C_WIN
        title = "⬆️ UPGRADE SUCCESSFUL! 🎉"
    else:
        color = C_LOSS
        title = "⬆️ UPGRADE FAILED! 💀"

    wheel = upgrader_wheel_render(display_chance, arrow_pos, outcome=outcome)

    stats = (
        f"┌─────────────────────────┐\
"
        f"│ 💰 **Bet** • {format_amount(bet)} 💎\
"
        f"│ 📊 **Multiplier** • {mult:.2f}x\
"
        f"│ 🎯 **Win Chance** • {display_chance*100:.2f}%\
"
        f"│ 💵 **Win Payout** • {format_amount(payout)} 💎\
"
    )
    if outcome == "win":
        stats += f"│ ✨ **Profit** • +{format_amount(profit)} 💎\
"
    elif outcome == "loss":
        stats += f"│ ❌ **Lost** • {format_amount(bet)} 💎\
"
    stats += "└─────────────────────────┘"

    embed = discord.Embed(
        title=title,
        description=f"```\
{wheel}\
```\
{stats}",
        color=color
    )
    _brand_embed(embed)
    return embed

@bot.tree.command(name="upgrader", description="Set a target multiplier and spin — higher targets = higher risk!")
@app_commands.describe(
    bet="Bet amount e.g. 5k, 1M",
    multiplier="Target multiplier (min 1.2). e.g. 1.2, 2.5, 10"
)
async def cmd_upgrader(interaction: discord.Interaction, bet: str, multiplier: float):
    wait = check_cooldown("upgrader", interaction.user.id)
    if wait > 0:
        await interaction.response.send_message(
            f"⏳ Wait **{wait:.1f}s** before playing again.", ephemeral=True)
        return
    if is_game_locked("upgrader", interaction.user):
        await interaction.response.send_message(
            "🔒 **Upgrader** is currently locked to staff only.", ephemeral=True)
        return

    if multiplier < UPGRADER_MIN_MULT:
        await interaction.response.send_message(
            f"❌ Minimum multiplier is **{UPGRADER_MIN_MULT}x**.", ephemeral=True)
        return
    if multiplier > UPGRADER_MAX_MULT:
        await interaction.response.send_message(
            f"❌ Maximum multiplier is **{UPGRADER_MAX_MULT}x**.", ephemeral=True)
        return

    amt = parse_amount(bet)
    if not amt or amt < MIN_BET:
        await interaction.response.send_message(
            f"❌ Minimum bet is **{format_amount(MIN_BET)}**.", ephemeral=True)
        return
    if amt > MAX_BET:
        await interaction.response.send_message(
            f"❌ Max bet is **{format_amount(MAX_BET)}**.", ephemeral=True)
        return

    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            row = await get_user(conn, interaction.user.id)
            if not row or row["balance"] < amt:
                bal = row["balance"] if row else 0
                await interaction.response.send_message(
                    f"❌ Insufficient balance — you have **{format_amount(bal)}** but need **{format_amount(amt)}**.",
                    ephemeral=True)
                return
            deducted = await deduct_balance_safe(conn, interaction.user.id, amt)
            if not deducted:
                await interaction.response.send_message("❌ Insufficient balance.", ephemeral=True)
                return
        finally:
            await release_conn(conn)

    real_chance = upgrader_real_chance(multiplier)
    display_chance = upgrader_display_chance(multiplier)
    _forced = _force_result.pop(interaction.user.id, None)
    if _forced == "win":   won = True
    elif _forced == "lose": won = False
    else:                    won = random.random() < real_chance
    outcome = "win" if won else "loss"
    payout = min(int(amt * multiplier), MAX_PAYOUT) if won else 0
    net = payout - amt

    win_segs = max(1, round(display_chance * UPGRADER_WHEEL_SIZE))
    win_boundary = win_segs / UPGRADER_WHEEL_SIZE
    if won:
        final_pos = random.uniform(0.0, win_boundary * 0.95)
    else:
        final_pos = random.uniform(win_boundary, 0.999)

    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    await interaction.response.send_message(
        embed=upgrader_embed(amt, multiplier, outcome="pending", arrow_pos=0.0))
    msg = await interaction.original_response()

    total_frames = 22
    for frame in range(total_frames):
        t = frame / total_frames
        eased = t * t * (3 - 2 * t)
        rotations = 3.0
        pos = ((rotations + final_pos) * eased) % 1.0

        try:
            await msg.edit(embed=upgrader_embed(amt, multiplier, outcome="spinning", arrow_pos=pos))
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass

        delay = 0.06 + 0.30 * eased
        await asyncio.sleep(delay)

    try:
        await msg.edit(embed=upgrader_embed(amt, multiplier, outcome=outcome, arrow_pos=final_pos))
    except Exception as _err:
        print(f"[ERROR] Failed to send error message: {_err}")
        pass

    conn = await get_conn()
    try:
        if payout > 0:
            payout = await apply_win_payout(conn, interaction.user.id, payout, amt, "upgrader")
        await record_game(conn, interaction.user.id, won, amt, payout, game="upgrader")
        await log_transaction(conn, interaction.user.id, "upgrader", net)
        if interaction.guild:
            row = await get_user(conn, interaction.user.id)
            member = interaction.guild.get_member(interaction.user.id)
            if row and member:
                await update_user_rank(member, row["wagered"])
    except Exception as e:
        print(f"[UPGRADER] DB error, refunding: {e}")
        try:
            await update_balance(conn, interaction.user.id, amt)
        except Exception as e:

            print(f"[ERROR] {type(e).__name__}: {e}")
            pass
    finally:
        await release_conn(conn)

    log_e = discord.Embed(title="⬆️ Upgrader Result", color=C_WIN if won else C_LOSS)
    log_e.add_field(name="Player",      value=interaction.user.mention,       inline=True)
    log_e.add_field(name="Bet",         value=format_amount(amt),             inline=True)
    log_e.add_field(name="Multiplier",  value=f"{multiplier:.2f}x",           inline=True)
    log_e.add_field(name="Shown Odds",  value=f"{display_chance*100:.2f}%",   inline=True)
    log_e.add_field(name="Payout",      value=format_amount(payout),          inline=True)
    log_e.add_field(name="Outcome",     value="✅ WIN" if won else "❌ LOSS",  inline=True)
    log_e.set_footer(text=now_ts())
    await send_log(log_e)
    _end_game_session(interaction.user.id)

async def ensure_verified_role(guild: discord.Guild) -> discord.Role | None:
    """Ensure the Verified role exists, create it if not."""
    if not guild:
        return None
    existing = discord.utils.get(guild.roles, name=VERIFIED_ROLE_NAME)
    if existing:
        return existing
    try:
        role = await guild.create_role(
            name=VERIFIED_ROLE_NAME,
            color=discord.Color(0x57F287),
            hoist=False,
            mentionable=False,
            reason="Auto-created Verified role"
        )
        print(f"[VERIFY] Created Verified role in {guild.name}")
        return role
    except Exception as e:
        print(f"[VERIFY] Failed to create Verified role in {guild.name}: {e}")
        return None

class VerifyView(discord.ui.View):
    """Verify button removed — kept as empty class to avoid breaking persistent view registration."""
    def __init__(self):
        super().__init__(timeout=None)

@bot.tree.command(name="sendverify", description="[Admin] Post the verification button and auto-lock all channels to Verified-only.")
@app_commands.describe(message="Optional custom message above the button")
@admin_only()
async def cmd_sendverify(interaction: discord.Interaction, message: str = None):
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild

    verified_role = await ensure_verified_role(guild)
    member_role   = await ensure_member_role(guild)

    locked = 0
    skipped = 0
    everyone = guild.default_role
    for channel in guild.text_channels:
        if channel.id == interaction.channel.id:
            try:
                await channel.set_permissions(everyone,       read_messages=True,  send_messages=False)
                await channel.set_permissions(verified_role,  read_messages=True,  send_messages=True)
            except Exception:
                pass
            continue
        try:
            await channel.set_permissions(everyone,      read_messages=False, send_messages=False)
            await channel.set_permissions(verified_role, read_messages=True,  send_messages=True)
            locked += 1
        except discord.Forbidden:
            skipped += 1
        except Exception as e:
            print(f"[VERIFY SETUP] Channel {channel.name}: {e}")
            skipped += 1

    conn = await get_conn()
    try:
        await conn.execute(
            "INSERT INTO bot_settings (key, value) VALUES ('verify_channel_id', $1) "
            "ON CONFLICT (key) DO UPDATE SET value=$1",
            str(interaction.channel.id)
        )
    finally:
        await release_conn(conn)

    desc = message or (
        "Click the button below to verify yourself and gain instant access to the server.\n\n"
        "**Takes 1 second — just click the button below.**"
    )
    embed = discord.Embed(
        title="🔐  Member Verification",
        description=desc,
        color=discord.Color(0x57F287)
    )
    embed.set_footer(text="One click — instant access.")
    await interaction.channel.send(embed=embed, view=VerifyView())

    await interaction.followup.send(
        f"✅ Done!\n"
        f"• **{locked}** channels locked to Verified-only\n"
        f"• **{skipped}** channels skipped (missing permissions)\n"
        f"• Verify button posted in {interaction.channel.mention}\n"
        f"• New members will be DM'd to verify before they can access anything",
        ephemeral=True
    )

@bot.tree.command(name="setverifylog", description="[Admin] Set channel where verifications are logged.")
@app_commands.describe(channel="Channel to log verifications in")
@admin_only()
async def cmd_setverifylog(interaction: discord.Interaction, channel: discord.TextChannel):
    conn = await get_conn()
    try:
        await conn.execute(
            "INSERT INTO bot_settings (key, value) VALUES ('verify_log_channel', $1) "
            "ON CONFLICT (key) DO UPDATE SET value=$1",
            str(channel.id)
        )
    finally:
        await release_conn(conn)
    await interaction.response.send_message(
        f"✅ Verification logs will be sent to {channel.mention}.", ephemeral=True)

@bot.tree.command(name="unverify", description="[Admin] Remove the Verified role from a user.")
@app_commands.describe(user="User to unverify")
@admin_only()
async def cmd_unverify(interaction: discord.Interaction, user: discord.Member):
    role = discord.utils.get(interaction.guild.roles, name=VERIFIED_ROLE_NAME)
    if not role or role not in user.roles:
        await interaction.response.send_message(f"⚠️ {user.mention} doesn't have the Verified role.", ephemeral=True)
        return
    try:
        await user.remove_roles(role, reason=f"Unverified by {interaction.user}")
    except discord.Forbidden:
        await interaction.response.send_message("❌ Missing permissions to remove role.", ephemeral=True)
        return
    await interaction.response.send_message(f"✅ Removed Verified role from {user.mention}.", ephemeral=True)

@bot.tree.command(name="setreward", description="[Admin] Set the gem reward for inviting a member with a 60+ day old account.")
@app_commands.describe(amount="Gem reward per valid invite e.g. 50k, 1M. Set to 0 to disable.")
async def cmd_setreward(interaction: discord.Interaction, amount: str):
    if not is_admin(interaction.user):
        await interaction.response.send_message("❌ Admins only.", ephemeral=True)
        return
    amt = parse_amount(amount) if amount != "0" else 0
    if amt is None:
        await interaction.response.send_message("❌ Invalid amount.", ephemeral=True)
        return
    conn = await get_conn()
    try:
        await conn.execute(
            """INSERT INTO bot_settings (key, value) VALUES ('invite_reward', $1)
               ON CONFLICT (key) DO UPDATE SET value=$1""",
            str(amt)
        )
    finally:
        await release_conn(conn)
    if amt == 0:
        await interaction.response.send_message("✅ Invite reward **disabled**.", ephemeral=True)
    else:
        await interaction.response.send_message(
            f"✅ Invite reward set to **{format_amount(amt)}** 💎 per valid invite.\
"
            f"*(Only triggers when the invited account is 60+ days old)*",
            ephemeral=True
        )

@bot.tree.command(name="setinvitelog", description="[Admin] Set the channel where invite rewards are logged.")
@app_commands.describe(channel="The channel to send invite reward notifications to")
async def cmd_setinvitelog(interaction: discord.Interaction, channel: discord.TextChannel):
    if not is_admin(interaction.user):
        await interaction.response.send_message("❌ Admins only.", ephemeral=True)
        return
    conn = await get_conn()
    try:
        await conn.execute(
            """INSERT INTO bot_settings (key, value) VALUES ('channel_invite_log', $1)
               ON CONFLICT (key) DO UPDATE SET value=$1""",
            str(channel.id)
        )
    finally:
        await release_conn(conn)
    global INVITE_LOG_ID
    INVITE_LOG_ID = channel.id
    await interaction.response.send_message(
        f"✅ Invite reward logs will now be sent to {channel.mention}.", ephemeral=True)

@bot.tree.command(name="setrewardlog", description="[Admin] Set the channel for rewards logs (rain, promo, daily, boost).")
@app_commands.describe(channel="The channel to send reward notifications to")
@admin_only()
async def cmd_setrewardlog(interaction: discord.Interaction, channel: discord.TextChannel):
    conn = await get_conn()
    try:
        await conn.execute(
            """INSERT INTO bot_settings (key, value) VALUES ('channel_reward_log', $1)
               ON CONFLICT (key) DO UPDATE SET value=$1""",
            str(channel.id)
        )
    finally:
        await release_conn(conn)
    global REWARD_LOG_ID
    REWARD_LOG_ID = channel.id
    await interaction.response.send_message(
        f"✅ Rewards log will now be sent to {channel.mention}.", ephemeral=True)

@bot.tree.command(name="setgamelog", description="[Admin] Set the channel where game results are logged.")
@app_commands.describe(channel="The game-log channel")
@admin_only()
async def cmd_setgamelog(interaction: discord.Interaction, channel: discord.TextChannel):
    conn = await get_conn()
    try:
        await conn.execute(
            """INSERT INTO bot_settings (key, value) VALUES ('channel_game_log', $1)
               ON CONFLICT (key) DO UPDATE SET value=$1""",
            str(channel.id)
        )
    finally:
        await release_conn(conn)
    global LOG_CHANNEL_ID
    LOG_CHANNEL_ID = channel.id
    await interaction.response.send_message(
        f"✅ Game log will now be sent to {channel.mention}.", ephemeral=True)

@bot.tree.command(name="setfinancelog", description="[Admin] Set the channel where deposits/withdrawals are logged.")
@app_commands.describe(channel="The finance-log channel")
@admin_only()
async def cmd_setfinancelog(interaction: discord.Interaction, channel: discord.TextChannel):
    conn = await get_conn()
    try:
        await conn.execute(
            """INSERT INTO bot_settings (key, value) VALUES ('channel_finance_log', $1)
               ON CONFLICT (key) DO UPDATE SET value=$1""",
            str(channel.id)
        )
    finally:
        await release_conn(conn)
    global FINANCE_LOG_ID
    FINANCE_LOG_ID = channel.id
    await interaction.response.send_message(
        f"✅ Finance log will now be sent to {channel.mention}.", ephemeral=True)

@bot.tree.command(name="settiplog", description="[Admin] Set the admin tip-log channel.")
@app_commands.describe(channel="The admin tip-log channel")
@admin_only()
async def cmd_settiplog(interaction: discord.Interaction, channel: discord.TextChannel):
    conn = await get_conn()
    try:
        await conn.execute(
            """INSERT INTO bot_settings (key, value) VALUES ('channel_tip_log', $1)
               ON CONFLICT (key) DO UPDATE SET value=$1""",
            str(channel.id)
        )
    finally:
        await release_conn(conn)
    global TIP_LOG_ID
    TIP_LOG_ID = channel.id
    await interaction.response.send_message(
        f"✅ Tip log will now be sent to {channel.mention}.", ephemeral=True)

@bot.tree.command(name="settippublic", description="[Admin] Set the public tipping announcement channel.")
@app_commands.describe(channel="The public tipping channel")
@admin_only()
async def cmd_settippublic(interaction: discord.Interaction, channel: discord.TextChannel):
    conn = await get_conn()
    try:
        await conn.execute(
            """INSERT INTO bot_settings (key, value) VALUES ('channel_tip_public', $1)
               ON CONFLICT (key) DO UPDATE SET value=$1""",
            str(channel.id)
        )
    finally:
        await release_conn(conn)
    global TIP_PUBLIC_LOG_ID
    TIP_PUBLIC_LOG_ID = channel.id
    await interaction.response.send_message(
        f"✅ Public tip announcements will now go to {channel.mention}.", ephemeral=True)

@bot.tree.command(name="managerewards", description="[Admin] Suspend or restore invite rewards for a user.")
@app_commands.describe(
    user="The target user",
    action="Whether to suspend or restore their invite rewards"
)
@app_commands.choices(action=[
    app_commands.Choice(name="Suspend", value="suspend"),
    app_commands.Choice(name="Restore", value="restore"),
])
@admin_only()
async def cmd_managerewards(interaction: discord.Interaction, user: discord.Member, action: str):
    conn = await get_conn()
    try:
        await conn.execute("""
            CREATE TABLE IF NOT EXISTS suspended_invite_rewards (
                user_id TEXT PRIMARY KEY,
                suspended_at TEXT NOT NULL,
                suspended_by TEXT NOT NULL
            )
        """)
        already = await conn.fetchrow("SELECT 1 FROM suspended_invite_rewards WHERE user_id=$1", str(user.id))

        if action == "suspend":
            if already:
                await interaction.response.send_message(f"⚠️ Invite rewards are already suspended for {user.mention}.", ephemeral=True)
                return
            await conn.execute(
                "INSERT INTO suspended_invite_rewards (user_id, suspended_at, suspended_by) VALUES ($1, $2, $3) ON CONFLICT DO NOTHING",
                str(user.id), now_ts(), str(interaction.user.id)
            )
            title, desc, color = "🔒 Invite Rewards Suspended", f"Invite rewards **suspended** for {user.mention}.", C_WARN
        else:
            if not already:
                await interaction.response.send_message(f"⚠️ Invite rewards are not currently suspended for {user.mention}.", ephemeral=True)
                return
            await conn.execute("DELETE FROM suspended_invite_rewards WHERE user_id=$1", str(user.id))
            title, desc, color = "✅ Invite Rewards Restored", f"Invite rewards **restored** for {user.mention}.", C_WIN
    finally:
        await release_conn(conn)

    embed = discord.Embed(title=title, description=desc, color=color)
    embed.set_footer(text=f"By {interaction.user} | {now_ts()}")
    await interaction.response.send_message(embed=embed)
    log_e = discord.Embed(title=title, color=color)
    log_e.add_field(name="User", value=user.mention,            inline=True)
    log_e.add_field(name="By",   value=interaction.user.mention, inline=True)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

@bot.tree.command(name="invitestats", description="Check how many successful invites you have and total earned.")
async def cmd_invitestats(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    conn = await get_conn()
    try:
        rows = await conn.fetch(
            "SELECT invitee_id, rewarded_at FROM invite_rewards WHERE inviter_id=$1 ORDER BY rewarded_at DESC",
            str(interaction.user.id)
        )
        setting = await conn.fetchrow("SELECT value FROM bot_settings WHERE key='invite_reward'")
    except Exception as e:
        print(f"[ERROR] invitestats: {type(e).__name__}: {e}")
        await interaction.followup.send("⚠️  Something went wrong — try again.", ephemeral=True)
        return
    finally:
        await release_conn(conn)

    reward_per = int(setting["value"]) if setting else 0
    total_invites = len(rows)
    total_earned = total_invites * reward_per

    embed = discord.Embed(title="📨 Your Invite Stats", color=C_BLUE)
    embed.add_field(name="Valid Invites",  value=str(total_invites),           inline=True)
    embed.add_field(name="Reward Each",   value=format_amount(reward_per),    inline=True)
    embed.add_field(name="Total Earned",  value=format_amount(total_earned),  inline=True)
    if rows:
        recent = "\
".join(f"• <@{r['invitee_id']}> — {r['rewarded_at']}" for r in rows[:5])
        embed.add_field(name="Recent Invites", value=recent, inline=False)
    embed.set_footer(text="Only accounts 60+ days old count as valid invites")
    await interaction.followup.send(embed=embed)

COINS_PER_DOLLAR = 10_000  # 10,000 gems = $1 (1 gem = $0.0001)

async def ensure_user_by_id(conn, user_id_str: str):
    """Ensure a user row exists by ID string (no Member object needed)."""
    await conn.execute(
        """INSERT INTO users (user_id, username, balance, created_at, last_updated)
           VALUES ($1, $2, 0, $3, $3)
           ON CONFLICT (user_id) DO NOTHING""",
        user_id_str, "unknown", now_ts()
    )

async def _get_stock(conn) -> list:
    """Return only in-stock rows ordered by unit_value desc."""
    return await conn.fetch(
        "SELECT item_name, quantity, unit_value FROM stock WHERE quantity > 0 ORDER BY unit_value DESC"
    )

async def _get_stock_item(conn, item_name: str):
    return await conn.fetchrow(
        "SELECT item_name, quantity, unit_value FROM stock WHERE item_name=$1",
        item_name
    )

async def _stock_embed(rows, page: int = 0, page_size: int = 10) -> discord.Embed:
    """Build the public /stock embed — numbered list, paginated."""
    e = discord.Embed(color=C_GOLD, title="📦  Stock Items")
    if not rows:
        e.description = "*No items currently in stock.*"
        _brand_embed(e)
        return e
    total   = len(rows)
    pages   = max(1, (total + page_size - 1) // page_size)
    page    = max(0, min(page, pages - 1))
    chunk   = rows[page * page_size:(page + 1) * page_size]
    lines   = []
    for idx, r in enumerate(chunk, start=page * page_size + 1):
        val  = r["unit_value"]
        name = r["item_name"]
        lines.append(f"{idx} **{name}** - Value: {format_amount(val)} 💎")
    e.description = "\n".join(lines)
    e.set_footer(text=f"Page {page+1}/{pages}  ·  Total Items: {total}")
    _brand_embed(e)
    return e

class WithdrawTicketView(discord.ui.View):
    """Buttons shown inside a withdrawal ticket channel (staff side).
    Uses dynamic custom_ids so multiple tickets can coexist.
    Registered as a persistent view on startup via _restore_ticket_views().
    """
    def __init__(self, ticket_id: int, user_id: int):
        super().__init__(timeout=None)
        self.ticket_id = ticket_id
        self.user_id   = user_id
        for item in self.children:
            if hasattr(item, 'custom_id'):
                if 'deliver' in item.custom_id:
                    item.custom_id = f"ticket_deliver_{ticket_id}"
                elif 'cancel' in item.custom_id:
                    item.custom_id = f"ticket_cancel_{ticket_id}"

    @discord.ui.button(label="✅ Mark Delivered", style=discord.ButtonStyle.green, custom_id="ticket_deliver")
    async def deliver_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not is_admin(interaction.user):
            await interaction.response.send_message("❌ Staff only.", ephemeral=True)
            return
        conn = await get_conn()
        try:
            row = await conn.fetchrow(
                "SELECT * FROM withdrawals_queue WHERE id=$1", self.ticket_id
            )
            if not row:
                await interaction.response.send_message("❌ Ticket not found.", ephemeral=True)
                return
            if row["status"] != "pending":
                await interaction.response.send_message(
                    f"❌ Already `{row['status']}`.", ephemeral=True
                )
                return
            await conn.execute(
                """UPDATE withdrawals_queue
                   SET status='completed', claimed_by=$1, completed_at=$2
                   WHERE id=$3""",
                str(interaction.user.id), now_ts(), self.ticket_id
            )
        finally:
            await release_conn(conn)

        for child in self.children:
            child.disabled = True
        await interaction.message.edit(view=self)

        done_e = discord.Embed(
            color=C_WIN,
            description=(
                f"## ✅  DELIVERED\n"
                f"> Marked as delivered by {interaction.user.mention}\n"
                f"> <@{self.user_id}> — your item has been sent!"
            )
        )
        done_e.set_footer(text=now_ts())
        await interaction.response.send_message(embed=done_e)

        log_e = discord.Embed(color=C_WIN, description="## ✅  WITHDRAWAL DELIVERED")
        log_e.add_field(name="Ticket",    value=str(self.ticket_id),         inline=True)
        log_e.add_field(name="User",      value=f"<@{self.user_id}>",        inline=True)
        log_e.add_field(name="Staff",     value=interaction.user.mention,    inline=True)
        log_e.set_footer(text=now_ts())
        await send_finance_log(log_e)

    @discord.ui.button(label="❌ Refund & Cancel", style=discord.ButtonStyle.red, custom_id="ticket_cancel")
    async def cancel_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not is_admin(interaction.user):
            await interaction.response.send_message("❌ Staff only.", ephemeral=True)
            return
        conn = await get_conn()
        try:
            row = await conn.fetchrow(
                "SELECT * FROM withdrawals_queue WHERE id=$1", self.ticket_id
            )
            if not row or row["status"] != "pending":
                await interaction.response.send_message(
                    "❌ Ticket not found or already closed.", ephemeral=True
                )
                return
            await update_balance(conn, int(row["user_id"]), row["total_cost"])
            await log_transaction(
                conn, int(row["user_id"]), "withdraw_refund", row["total_cost"],
                f"Ticket #{self.ticket_id} cancelled by {interaction.user}"
            )
            await conn.execute(
                "UPDATE stock SET quantity = quantity + $1 WHERE item_name = $2",
                row["quantity"], row["item_name"]
            )
            await conn.execute(
                """UPDATE withdrawals_queue
                   SET status='cancelled', claimed_by=$1, completed_at=$2
                   WHERE id=$3""",
                str(interaction.user.id), now_ts(), self.ticket_id
            )
        finally:
            await release_conn(conn)

        for child in self.children:
            child.disabled = True
        await interaction.message.edit(view=self)

        refund_e = discord.Embed(
            color=C_LOSS,
            description=(
                f"## ❌  TICKET CANCELLED\n"
                f"> Cancelled by {interaction.user.mention}\n"
                f"> <@{self.user_id}> — your gems have been refunded."
            )
        )
        refund_e.set_footer(text=now_ts())
        await interaction.response.send_message(embed=refund_e)

        log_e = discord.Embed(color=C_LOSS, description="## ❌  WITHDRAWAL CANCELLED")
        log_e.add_field(name="Ticket",  value=str(self.ticket_id),       inline=True)
        log_e.add_field(name="User",    value=f"<@{self.user_id}>",      inline=True)
        log_e.add_field(name="Staff",   value=interaction.user.mention,  inline=True)
        log_e.set_footer(text=now_ts())
        await send_finance_log(log_e)

@bot.tree.command(name="deposit", description="Open a deposit ticket — staff will credit your gems.")
async def cmd_deposit(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)

    guild = bot.get_guild(GUILD_ID)
    ticket_ch = None
    if guild:
        deposits_cat = discord.utils.get(guild.categories, name="Deposits")
        if deposits_cat:
            ticket_ch = discord.utils.get(guild.text_channels, category=deposits_cat)
        if not ticket_ch:
            ticket_ch = discord.utils.find(
                lambda c: "deposit" in c.name.lower() and isinstance(c, discord.TextChannel),
                guild.channels
            )

    ticket_id = f"{int(discord.utils.time_snowflake(discord.utils.utcnow()) & 0xFFFF):04X}"
    ticket_channel = None

    if ticket_ch and guild:
        try:
            staff_role = discord.utils.get(guild.roles, name=STAFF_ROLE_NAME)
            admin_role = discord.utils.get(guild.roles, name=ADMIN_ROLE_NAME)
            overwrites = {
                guild.default_role: discord.PermissionOverwrite(read_messages=False),
                guild.me:           discord.PermissionOverwrite(read_messages=True, send_messages=True, manage_channels=True),
                interaction.user:   discord.PermissionOverwrite(read_messages=True, send_messages=True),
            }
            if staff_role: overwrites[staff_role] = discord.PermissionOverwrite(read_messages=True, send_messages=True)
            if admin_role: overwrites[admin_role] = discord.PermissionOverwrite(read_messages=True, send_messages=True)

            ticket_channel = await guild.create_text_channel(
                name=f"deposit-{interaction.user.name}-{ticket_id}",
                category=deposits_cat or ticket_ch.category,
                overwrites=overwrites,
                reason=f"Deposit ticket for {interaction.user}"
            )

            ticket_e = discord.Embed(
                color=C_GOLD,
                description=(
                    f"## 🎫  DEPOSIT TICKET\n"
                    f"{interaction.user.mention} wants to make a deposit.\n"
                    f"Staff — please handle this deposit and credit their gems.\n\n"
                    f"> **Tell the user how much to send and where.**"
                )
            )
            ticket_e.add_field(name="👤 User",      value=interaction.user.mention, inline=True)
            ticket_e.add_field(name="🆔 Ticket ID", value=f"`{ticket_id}`",         inline=True)
            ticket_e.add_field(name="⏳ Status",    value="`PENDING`",               inline=True)
            _brand_embed(ticket_e)
            await ticket_channel.send(embed=ticket_e)
        except Exception as ex:
            print(f"[DEPOSIT TICKET] Could not create channel: {ex}")
            ticket_channel = None

    reply_e = discord.Embed(
        color=C_GOLD,
        description=(
            f"## 🎫  DEPOSIT TICKET OPENED\n"
            f"{'Your private ticket: ' + ticket_channel.mention if ticket_channel else 'A ticket has been opened for you.'}\n\n"
            f"Staff will contact you with payment details shortly."
        )
    )
    _brand_embed(reply_e)
    await interaction.followup.send(embed=reply_e, ephemeral=True)

    log_e = discord.Embed(color=C_GOLD, description="## 🎫  DEPOSIT TICKET OPENED")
    log_e.add_field(name="User",      value=interaction.user.mention,            inline=True)
    log_e.add_field(name="Ticket ID", value=f"`{ticket_id}`",                    inline=True)
    if ticket_channel:
        log_e.add_field(name="Channel", value=ticket_channel.mention,            inline=True)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

class WithdrawSelectView(discord.ui.View):
    """Shows a dropdown of items the user can afford."""
    def __init__(self, rows, user_bal):
        super().__init__(timeout=60)
        options = []
        for r in rows[:25]:
            gem_str = format_amount(r["unit_value"])
            options.append(discord.SelectOption(
                label=r["item_name"][:100],
                value=r["item_name"][:100],
                description=f"{gem_str} gems",
                emoji="💎"
            ))
        sel = discord.ui.Select(placeholder="Choose an item to withdraw...", options=options)
        sel.callback = self._on_select
        self.add_item(sel)
        self._chosen = None

    async def _on_select(self, interaction: discord.Interaction):
        self._chosen = interaction.data["values"][0]
        await interaction.response.defer()
        self.stop()

    async def on_timeout(self):
        for c in self.children: c.disabled = True

@bot.tree.command(name="withdraw", description="Spend your gems to withdraw an item from the stock shop.")
async def cmd_withdraw(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)

    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        user_row = await get_user(conn, interaction.user.id)
        bal = user_row["balance"] if user_row else 0
        all_rows = await _get_stock(conn)
    finally:
        await release_conn(conn)

    affordable = [r for r in all_rows if r["unit_value"] <= bal and r["quantity"] > 0]
    if not affordable:
        await interaction.followup.send(
            "❌ No items available that match your balance. Use `/stock` to see all items.",
            ephemeral=True
        )
        return

    view = WithdrawSelectView(affordable, bal)
    sel_embed = discord.Embed(
        color=C_GOLD,
        title="📦  Withdraw Item",
        description=(
            f"Your balance: **{format_amount(bal)}** 💎\n"
            f"Select an item you can afford:"
        )
    )
    _brand_embed(sel_embed)
    await interaction.followup.send(embed=sel_embed, view=view, ephemeral=True)

    await view.wait()
    if not view._chosen:
        return

    item = view._chosen
    quantity = 1

    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        stock_row = await _get_stock_item(conn, item)
        if not stock_row:
            await interaction.followup.send(
                f"❌ Item `{item}` not found in stock. Use `/stock` to see available items.",
                ephemeral=True
            )
            return
        if stock_row["quantity"] < quantity:
            avail = stock_row["quantity"]
            await interaction.followup.send(
                f"❌ Only **{avail}** `{item}` in stock — you requested {quantity}.",
                ephemeral=True
            )
            return

        total_cost = stock_row["unit_value"] * quantity
        user_row   = await get_user(conn, interaction.user.id)
        bal        = user_row["balance"] if user_row else 0

        wr_row = await conn.fetchrow(
            "SELECT required_amt, wagered_so_far, req_met FROM wager_requirements WHERE user_id=$1",
            str(interaction.user.id)
        )
        if wr_row and not wr_row["req_met"]:
            remaining = wr_row["required_amt"] - wr_row["wagered_so_far"]
            await interaction.followup.send(
                f"❌ You have a pending wager requirement of **{format_amount(remaining)} 💎** before you can withdraw.\n"
                f"Progress: **{format_amount(wr_row['wagered_so_far'])} / {format_amount(wr_row['required_amt'])}**",
                ephemeral=True
            )
            return

        if bal < total_cost:
            needed_usd = total_cost / COINS_PER_DOLLAR
            await interaction.followup.send(
                f"❌ You need **{format_amount(total_cost)} gems** (`${needed_usd:.0f}`) "
                f"but only have **{format_amount(bal)} gems**.",
                ephemeral=True
            )
            return

        ok = await deduct_balance_safe(conn, interaction.user.id, total_cost)
        if not ok:
            await interaction.followup.send("❌ Insufficient balance.", ephemeral=True)
            return

        await conn.execute(
            "UPDATE stock SET quantity = quantity - $1 WHERE item_name = $2",
            quantity, item
        )
        await conn.execute(
            "DELETE FROM stock WHERE item_name = $1 AND quantity <= 0",
            item
        )

        ticket_id = await conn.fetchval(
            """INSERT INTO withdrawals_queue
               (user_id, username, item_name, quantity, total_cost, channel_id, status, created_at)
               VALUES ($1, $2, $3, $4, $5, $6, 'pending', $7)
               RETURNING id""",
            str(interaction.user.id),
            str(interaction.user),
            item,
            quantity,
            total_cost,
            "",
            now_ts()
        )
        await log_transaction(
            conn, interaction.user.id, "stock_withdraw", -total_cost,
            f"Withdrew {quantity}x {item} (ticket #{ticket_id})"
        )
    finally:
        await release_conn(conn)

    usd_val = total_cost / COINS_PER_DOLLAR

    guild = bot.get_guild(GUILD_ID)
    thread = None
    ticket_ch = None
    if guild:
        withdraws_cat = discord.utils.get(guild.categories, name="Withdraws")
        if withdraws_cat:
            ticket_ch = discord.utils.get(guild.text_channels, category=withdraws_cat)
        if not ticket_ch:
            ticket_ch = discord.utils.find(
                lambda c: "withdraw" in c.name.lower() and isinstance(c, discord.TextChannel),
                guild.channels
            )
    if ticket_ch and guild:
        try:
            staff_role = discord.utils.get(guild.roles, name=STAFF_ROLE_NAME)
            admin_role = discord.utils.get(guild.roles, name=ADMIN_ROLE_NAME)
            owner_role = discord.utils.get(guild.roles, name=OWNER_ROLE_NAME)
            overwrites = {
                guild.default_role:                discord.PermissionOverwrite(read_messages=False),
                guild.me:                          discord.PermissionOverwrite(read_messages=True, send_messages=True, manage_channels=True),
                interaction.user:                  discord.PermissionOverwrite(read_messages=True, send_messages=True),
            }
            if staff_role: overwrites[staff_role] = discord.PermissionOverwrite(read_messages=True, send_messages=True)
            if admin_role: overwrites[admin_role] = discord.PermissionOverwrite(read_messages=True, send_messages=True)
            if owner_role: overwrites[owner_role] = discord.PermissionOverwrite(read_messages=True, send_messages=True)

            target_category = ticket_ch.category

            thread = await guild.create_text_channel(
                name=f"withdraw-{interaction.user.name}",
                category=target_category,
                overwrites=overwrites,
                reason=f"Withdrawal ticket #{ticket_id} for {interaction.user}"
            )

            conn2 = await get_conn()
            try:
                await conn2.execute(
                    "UPDATE withdrawals_queue SET channel_id=$1 WHERE id=$2",
                    str(thread.id), ticket_id
                )
            finally:
                await release_conn(conn2)

            ticket_e = discord.Embed(color=0x2b2d31)
            ticket_e.description = (
                f"🚀 **Withdrawal Request**\n\n"
                f"**Requester**\n"
                f"{interaction.user.mention}\n\n"
                f"**Requested Items**\n"
                f"- {item} x{quantity} - {format_amount(total_cost)} 💎\n\n"
                f"**Total Value**\n"
                f"{format_amount(total_cost)} 💎\n\n"
                f"⚠️ **Important Information**\n"
                f"• Do not spam ping staff members\n"
                f"• Staff will process your withdrawal as soon as possible\n"
                f"• This ticket will be handled by an administrator\n"
                f"• Make sure to provide any additional details if needed\n\n"
                f"User ID: {interaction.user.id} • Ticket ID: {ticket_id}"
            )

            view = WithdrawTicketView(ticket_id=ticket_id, user_id=interaction.user.id)
            ping_content = f"{interaction.user.mention}"
            if staff_role: ping_content += f" {staff_role.mention}"
            await thread.send(content=ping_content, embed=ticket_e, view=view)

            try:
                withdraw_log_ch = discord.utils.get(guild.text_channels, name="🚨┃withdraws")
                if withdraw_log_ch:
                    log_ticket_e = discord.Embed(
                        color=0xFFA500,
                        description=(
                            f"📤 **New Withdrawal Ticket**\n\n"
                            f"**Requester:** {interaction.user.mention} (`{interaction.user.id}`)\n"
                            f"**Ticket Channel:** {thread.mention}\n\n"
                            f"**Requested Items**\n"
                            f"- {item} x{quantity} - {format_amount(total_cost)} 💎\n\n"
                            f"**Total Value:** {format_amount(total_cost)} 💎\n\n"
                            f"User ID: {interaction.user.id} • Ticket ID: {ticket_id}"
                        )
                    )
                    _brand_embed(log_ticket_e)
                    await withdraw_log_ch.send(embed=log_ticket_e)
            except Exception as log_ex:
                print(f"[WITHDRAW LOG] Could not post to withdraws: {log_ex}")

            try:
                public_wd_ch = discord.utils.get(guild.text_channels, name="📤｜withdrawals")
                if not public_wd_ch:
                    for ch in guild.text_channels:
                        if "withdrawal" in ch.name.lower():
                            public_wd_ch = ch
                            break
                if not public_wd_ch:
                    public_wd_ch = await guild.create_text_channel(
                        name="📤｜withdrawals",
                        reason="Auto-created for withdrawal notifications"
                    )
                if public_wd_ch:
                    pub_wd_e = discord.Embed(
                        color=0x5865F2,
                        description=(
                            f"## 📤  WITHDRAWAL SUBMITTED\n\n"
                            f"**{interaction.user.mention}** just submitted a withdrawal!\n\n"
                            f"**Item:** {item} ×{quantity}\n"
                            f"**Value:** {format_amount(total_cost)} 💎\n"
                            f"**Ticket:** {thread.mention if thread else f'#{ticket_id}'}"
                        )
                    )
                    pub_wd_e.set_thumbnail(url=await get_avatar(interaction.user))
                    _brand_embed(pub_wd_e)
                    await public_wd_ch.send(embed=pub_wd_e)
            except Exception as pub_ex:
                print(f"[WITHDRAW PUBLIC LOG] {pub_ex}")

        except Exception as ex:
            print(f"[WITHDRAW TICKET] Thread creation failed: {ex}")
            thread = None

    reply_e = discord.Embed(
        color=C_WIN,
        description=(
            f"## 📦  WITHDRAWAL REQUESTED\n"
            f"{'Ticket: ' + thread.mention + chr(10) if thread else ''}"
            f"```diff\n"
            f"- {format_amount(total_cost)} gems\n"
            f"+ {quantity}x {item}\n"
            f"```\n"
            f"Staff will deliver your item shortly."
        )
    )
    reply_e.add_field(name="Item",      value=f"`{item}`",                  inline=True)
    reply_e.add_field(name="Quantity",  value=str(quantity),                inline=True)
    reply_e.add_field(name="Cost",      value=f"`{format_amount(total_cost)} gems`", inline=True)
    reply_e.add_field(name="USD",       value=f"`${usd_val:.0f}`",          inline=True)
    reply_e.add_field(name="Ticket ID", value=f"`#{ticket_id}`",            inline=True)
    _brand_embed(reply_e)

    await interaction.followup.send(embed=reply_e, ephemeral=True)

    log_e = discord.Embed(color=C_WARN, description="## 📦  STOCK WITHDRAWAL")
    log_e.add_field(name="User",      value=interaction.user.mention,       inline=True)
    log_e.add_field(name="Item",      value=f"`{item}`",                    inline=True)
    log_e.add_field(name="Qty",       value=str(quantity),                  inline=True)
    log_e.add_field(name="Cost",      value=format_amount(total_cost),      inline=True)
    log_e.add_field(name="USD",       value=f"${usd_val:.0f}",              inline=True)
    log_e.add_field(name="Ticket",    value=f"#{ticket_id}",                inline=True)
    if thread:
        log_e.add_field(name="Thread", value=thread.mention,                inline=False)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

@bot.tree.command(name="stock", description="View all items in the shop available for withdrawal.")
async def cmd_stock(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    conn = await get_conn()
    try:
        rows = await _get_stock(conn)
    finally:
        await release_conn(conn)
    embed = await _stock_embed(rows)
    await interaction.followup.send(embed=embed, ephemeral=True)

@bot.tree.command(name="addstock", description="[Admin] Add an item to the stock shop.")
@app_commands.describe(
    item="Item name (e.g. 'Roblox $5 Gift Card')",
    value="Value in gems e.g. 70M, 100M, 500K"
)
@admin_only()
async def cmd_addstock(
    interaction: discord.Interaction,
    item: str,
    value: str
):
    await interaction.response.defer(ephemeral=True)

    parsed_value = parse_amount(value)
    if not parsed_value or parsed_value < 1:
        await interaction.followup.send("❌ Invalid value. Use e.g. `70M`, `100M`, `500K`.", ephemeral=True)
        return
    unit_value = parsed_value

    item = item.strip()
    conn = await get_conn()
    try:
        existing = await _get_stock_item(conn, item)
        if existing:
            await conn.execute(
                """UPDATE stock
                   SET quantity   = quantity + 1,
                       unit_value = $1
                   WHERE item_name = $2""",
                unit_value, item
            )
            action  = "restocked"
            new_qty = existing["quantity"] + 1
        else:
            await conn.execute(
                "INSERT INTO stock (item_name, quantity, unit_value) VALUES ($1, 1, $2)",
                item, unit_value
            )
            action  = "added"
            new_qty = 1
    finally:
        await release_conn(conn)

    usd = unit_value / COINS_PER_DOLLAR
    embed = discord.Embed(
        color=C_WIN,
        description=f"## ✅  Stock {action.upper()}"
    )
    embed.add_field(name="Item",      value=f"`{item}`",                                      inline=True)
    embed.add_field(name="In Stock",  value=str(new_qty),                                     inline=True)
    embed.add_field(name="Value",     value=f"`{format_amount(unit_value)} gems` (`${usd:.0f}`)", inline=True)
    embed.set_footer(text=f"{interaction.user}  ·  {now_ts()}")
    await interaction.followup.send(embed=embed, ephemeral=True)

    log_e = discord.Embed(color=C_WIN, description=f"## ✅  STOCK {action.upper()}")
    log_e.add_field(name="Admin",      value=interaction.user.mention, inline=True)
    log_e.add_field(name="Item",       value=f"`{item}`",              inline=True)
    log_e.add_field(name="In Stock",   value=str(new_qty),             inline=True)
    log_e.add_field(name="Value",      value=format_amount(unit_value),inline=True)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

@bot.tree.command(name="removestock", description="[Admin] Remove an item from the stock shop.")
@app_commands.describe(item="Exact item name to remove")
@admin_only()
async def cmd_removestock(
    interaction: discord.Interaction,
    item: str
):
    await interaction.response.defer(ephemeral=True)

    item = item.strip()
    conn = await get_conn()
    try:
        existing = await _get_stock_item(conn, item)
        if not existing:
            await interaction.followup.send(
                f"❌ Item `{item}` not found in stock.", ephemeral=True
            )
            return

        old_qty = existing["quantity"]

        if old_qty <= 1:
            await conn.execute("DELETE FROM stock WHERE item_name=$1", item)
            action  = "deleted"
            new_qty = 0
        else:
            await conn.execute(
                "UPDATE stock SET quantity = quantity - 1 WHERE item_name = $1",
                item
            )
            action  = "reduced"
            new_qty = old_qty - 1
    finally:
        await release_conn(conn)

    embed = discord.Embed(
        color=C_LOSS,
        description=f"## 🗑️  Stock {action.upper()}"
    )
    embed.add_field(name="Item",      value=f"`{item}`", inline=True)
    embed.add_field(name="Remaining", value=str(new_qty) if new_qty > 0 else "❌ Removed", inline=True)
    embed.set_footer(text=f"{interaction.user}  ·  {now_ts()}")
    await interaction.followup.send(embed=embed, ephemeral=True)

    log_e = discord.Embed(color=C_LOSS, description=f"## 🗑️  STOCK {action.upper()}")
    log_e.add_field(name="Admin",     value=interaction.user.mention, inline=True)
    log_e.add_field(name="Item",      value=f"`{item}`",              inline=True)
    log_e.add_field(name="Remaining", value=str(new_qty),             inline=True)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

@bot.tree.command(name="adminbalance", description="Check your admin insurance balance and how much you've used.")
@admin_only()
async def cmd_adminbalance(interaction: discord.Interaction):
    conn = await get_conn()
    try:
        row = await conn.fetchrow(
            "SELECT insurance, used FROM admin_balances WHERE admin_id=$1",
            str(interaction.user.id)
        )
    except Exception as e:
        print(f"[ERROR] adminbalance: {type(e).__name__}: {e}")
        await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
        return
    finally:
        await release_conn(conn)

    if not row:
        await interaction.response.send_message(
            "❌ You have no insurance balance set. Ask the owner to run `/setadminbalance`.",
            ephemeral=True
        )
        return

    insurance = row["insurance"]
    used      = row["used"]
    remaining = max(0, insurance - used)
    pct       = (used / insurance * 100) if insurance > 0 else 0
    bar_len   = 16
    filled    = int((used / insurance) * bar_len) if insurance > 0 else 0
    bar       = "█" * filled + "░" * (bar_len - filled)

    embed = discord.Embed(title="🛡️ Your Admin Insurance Balance", color=C_GOLD)
    embed.add_field(name="💰 Total Insurance", value=format_amount(insurance), inline=True)
    embed.add_field(name="📤 Used",            value=format_amount(used),      inline=True)
    embed.add_field(name="✅ Remaining",        value=format_amount(remaining), inline=True)
    embed.add_field(name="📊 Usage",           value=f"`[{bar}]` {pct:.1f}%",  inline=False)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed, ephemeral=True)

@bot.tree.command(name="setadminbalance", description="[Owner] Set an admin's insurance balance (their deposit credit limit).")
@app_commands.describe(admin="The admin to configure", amount="Insurance amount e.g. 10M")
@admin_only()
async def cmd_setadminbalance(interaction: discord.Interaction, admin: discord.Member, amount: str):
    amt = parse_amount(amount)
    if not amt or amt <= 0:
        await interaction.response.send_message("❌ Invalid amount.", ephemeral=True)
        return

    conn = await get_conn()
    try:
        await conn.execute(
            """INSERT INTO admin_balances (admin_id, insurance, used, last_updated)
               VALUES ($1, $2, 0, $3)
               ON CONFLICT (admin_id) DO UPDATE SET
                   insurance    = $2,
                   used         = 0,
                   last_updated = $3""",
            str(admin.id), amt, now_ts()
        )
    finally:
        await release_conn(conn)

    embed = discord.Embed(title="🛡️ Admin Insurance Set", color=C_GOLD)
    embed.add_field(name="Admin",     value=admin.mention,            inline=True)
    embed.add_field(name="Insurance", value=format_amount(amt),       inline=True)
    embed.add_field(name="Set By",    value=interaction.user.mention, inline=True)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed)
    await send_finance_log(embed)

@bot.tree.command(name="payadminbalance", description="[Owner] Top up an admin's insurance when they pay more.")
@app_commands.describe(admin="The admin who paid", amount="Amount they paid e.g. 5M")
@admin_only()
async def cmd_payadminbalance(interaction: discord.Interaction, admin: discord.Member, amount: str):
    amt = parse_amount(amount)
    if not amt or amt <= 0:
        await interaction.response.send_message("❌ Invalid amount.", ephemeral=True)
        return

    conn = await get_conn()
    try:
        existing = await conn.fetchrow(
            "SELECT insurance, used FROM admin_balances WHERE admin_id=$1",
            str(admin.id)
        )
        if not existing:
            await conn.execute(
                "INSERT INTO admin_balances (admin_id, insurance, used, last_updated) VALUES ($1, $2, 0, $3)",
                str(admin.id), amt, now_ts()
            )
            new_insurance = amt
            new_used = 0
        else:
            new_insurance = existing["insurance"] + amt
            new_used      = existing["used"]
            await conn.execute(
                "UPDATE admin_balances SET insurance=$1, last_updated=$2 WHERE admin_id=$3",
                new_insurance, now_ts(), str(admin.id)
            )
    finally:
        await release_conn(conn)

    remaining = max(0, new_insurance - new_used)
    embed = discord.Embed(title="💰 Admin Insurance Topped Up", color=C_WIN)
    embed.add_field(name="Admin",           value=admin.mention,               inline=True)
    embed.add_field(name="Paid",            value=format_amount(amt),          inline=True)
    embed.add_field(name="Total Insurance", value=format_amount(new_insurance), inline=True)
    embed.add_field(name="Used",            value=format_amount(new_used),     inline=True)
    embed.add_field(name="Remaining",       value=format_amount(remaining),    inline=True)
    embed.add_field(name="By",              value=interaction.user.mention,    inline=True)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed)
    await send_finance_log(embed)

@bot.tree.command(name="addcoins", description="[Admin] Adjust a user's account.")
@app_commands.describe(user="Target user", amount="Amount e.g. 5k, 1M")
@admin_only()
async def cmd_addcoins(interaction: discord.Interaction, user: discord.Member, amount: str):
    amt = parse_amount(amount)
    if not amt or amt <= 0:
        await interaction.response.send_message("❌ Invalid amount.", ephemeral=True)
        return

    conn = await get_conn()
    try:
        ab_row = await conn.fetchrow(
            "SELECT insurance, used FROM admin_balances WHERE admin_id=$1",
            str(interaction.user.id)
        )
    finally:
        await release_conn(conn)

    if ab_row is not None:
        remaining = ab_row["insurance"] - ab_row["used"]
        if amt > remaining:
            block_embed = discord.Embed(
                title="🚫 Admin Credit Limit Exceeded",
                description=(
                    f"{interaction.user.mention} tried to credit **{format_amount(amt)}** to {user.mention} "
                    f"but only has **{format_amount(max(0, remaining))}** insurance remaining.\n\n"
                    f"**Total Insurance:** {format_amount(ab_row['insurance'])}\n"
                    f"**Used:** {format_amount(ab_row['used'])}\n"
                    f"**Remaining:** {format_amount(max(0, remaining))}\n"
                    f"**Attempted:** {format_amount(amt)}"
                ),
                color=C_LOSS
            )
            block_embed.set_footer(text=now_ts())
            await send_finance_log(block_embed)
            await interaction.response.send_message(
                f"❌ You've exceeded your insurance limit. You can only credit **{format_amount(max(0, remaining))}** more.\n"
                f"Ask the owner to top up your balance with `/payadminbalance`.",
                ephemeral=True
            )
            return

    conn = await get_conn()
    try:
        await ensure_user(conn, user)
        old_bal = (await get_user(conn, user.id))["balance"]
        await update_balance(conn, user.id, amt)
        new_bal = (await get_user(conn, user.id))["balance"]
        await log_transaction(conn, user.id, "addcoins", amt, f"by {interaction.user.id}")
        await conn.execute(
            "UPDATE users SET total_deposited = total_deposited + $1 WHERE user_id = $2",
            amt, str(user.id)
        )
        if ab_row is not None:
            await conn.execute(
                "UPDATE admin_balances SET used = used + $1, last_updated = $2 WHERE admin_id = $3",
                amt, now_ts(), str(interaction.user.id)
            )
        await conn.execute(
            """INSERT INTO wager_requirements (user_id, required_amt, wagered_so_far, req_met)
               VALUES ($1, $2, 0, FALSE)
               ON CONFLICT (user_id) DO UPDATE SET
                   required_amt   = CASE WHEN wager_requirements.req_met THEN $2
                                         ELSE wager_requirements.required_amt + $2 END,
                   wagered_so_far = CASE WHEN wager_requirements.req_met THEN 0
                                         ELSE wager_requirements.wagered_so_far END,
                   req_met        = FALSE""",
            str(user.id), amt
        )
        row = await get_user(conn, user.id)
        if row and interaction.guild:
            member = interaction.guild.get_member(user.id)
            if member:
                await update_user_rank(member, row["wagered"])
    finally:
        await release_conn(conn)

    embed = discord.Embed(title="✅ Gems Added", color=C_WIN)
    embed.add_field(name="User",        value=user.mention,             inline=True)
    embed.add_field(name="Added",       value=format_amount(amt),       inline=True)
    embed.add_field(name="Old Balance", value=format_amount(old_bal),   inline=True)
    embed.add_field(name="New Balance", value=format_amount(new_bal),   inline=True)
    embed.add_field(name="Admin",       value=interaction.user.mention, inline=True)
    if ab_row is not None:
        new_remaining = max(0, ab_row["insurance"] - ab_row["used"] - amt)
        embed.add_field(name="🛡️ Your Remaining Limit", value=format_amount(new_remaining), inline=True)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed)
    await send_finance_log(embed)

@bot.tree.command(name="removecoins", description="[Admin] Modify a user's account.")
@app_commands.describe(user="Target user", amount="Amount e.g. 5k, 1M")
@admin_only()
async def cmd_removecoins(interaction: discord.Interaction, user: discord.Member, amount: str):
    amt = parse_amount(amount)
    if not amt or amt <= 0:
        await interaction.response.send_message("❌ Invalid amount.", ephemeral=True)
        return

    conn = await get_conn()
    try:
        await ensure_user(conn, user)
        old_bal = (await get_user(conn, user.id))["balance"]
        deducted = await deduct_balance_safe(conn, user.id, amt)
        if not deducted:
            await interaction.response.send_message(
                f"❌ User only has **{format_amount(old_bal)}**.", ephemeral=True)
            return
        new_bal = (await get_user(conn, user.id))["balance"]
        await log_transaction(conn, user.id, "removecoins", -amt, f"by {interaction.user.id}")
    finally:
        await release_conn(conn)

    embed = discord.Embed(title="✅ Gems Removed", color=C_LOSS)
    embed.add_field(name="User",        value=user.mention,           inline=True)
    embed.add_field(name="Removed",     value=format_amount(amt),     inline=True)
    embed.add_field(name="Old Balance", value=format_amount(old_bal), inline=True)
    embed.add_field(name="New Balance", value=format_amount(new_bal), inline=True)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed)
    await send_finance_log(embed)

@bot.tree.command(name="paystaff", description="[Owner] Pay a staff member 10% of their total added coins as a bonus.")
@app_commands.describe(staff_member="The staff member to pay (t-Mod, Moderator, Admin, or Manager)")
@owner_only()
async def cmd_paystaff(interaction: discord.Interaction, staff_member: discord.Member):
    """
    Pays 10% of the total coins the staff member added (their admin_balance 'used' amount)
    into their normal balance, then resets their used amount to 0.
    Only usable on t-Mod, Moderator, Admin, or Manager roles.
    """
    ELIGIBLE_ROLES = {TMOD_ROLE_NAME, STAFF_ROLE_NAME, ADMIN_ROLE_NAME, MANAGER_ROLE_NAME}
    member_roles   = {r.name for r in staff_member.roles}

    if not ELIGIBLE_ROLES.intersection(member_roles):
        await interaction.response.send_message(
            f"❌ {staff_member.mention} must have one of these roles: "
            f"**t-Mod**, **Moderator**, **Admin**, or **Manager**.",
            ephemeral=True
        )
        return

    conn = await get_conn()
    try:
        await ensure_user(conn, staff_member)

        ab_row = await conn.fetchrow(
            "SELECT insurance, used FROM admin_balances WHERE admin_id=$1",
            str(staff_member.id)
        )

        if not ab_row or ab_row["used"] <= 0:
            await interaction.response.send_message(
                f"❌ {staff_member.mention} has no recorded coins added. "
                f"They need to use `/addcoins` first so their contribution is tracked.",
                ephemeral=True
            )
            return

        total_added = ab_row["used"]
        bonus       = int(total_added * 0.10)   # 10% of what they added

        if bonus <= 0:
            await interaction.response.send_message(
                f"❌ The 10% bonus on {format_amount(total_added)} is too small to pay out.",
                ephemeral=True
            )
            return

        old_bal = (await get_user(conn, staff_member.id))["balance"]
        await update_balance(conn, staff_member.id, bonus)
        new_bal = (await get_user(conn, staff_member.id))["balance"]

        await conn.execute(
            "UPDATE admin_balances SET used=0, last_updated=$1 WHERE admin_id=$2",
            now_ts(), str(staff_member.id)
        )

        await log_transaction(
            conn, staff_member.id, "paystaff_bonus", bonus,
            f"10% staff pay on {format_amount(total_added)} added — by {interaction.user.id}"
        )
    finally:
        await release_conn(conn)

    embed = discord.Embed(
        title="💸  Staff Pay — 10% Bonus",
        color=C_WIN,
        description=(
            f"{staff_member.mention} has been paid their weekly staff bonus!\n\n"
            f"```diff\n"
            f"+ {format_amount(bonus)} gems (10% bonus)\n"
            f"# Total coins added this period: {format_amount(total_added)}\n"
            f"```"
        )
    )
    embed.add_field(name="Staff",         value=staff_member.mention,        inline=True)
    embed.add_field(name="Coins Added",   value=format_amount(total_added),  inline=True)
    embed.add_field(name="Bonus (10%)",   value=format_amount(bonus),        inline=True)
    embed.add_field(name="Old Balance",   value=format_amount(old_bal),      inline=True)
    embed.add_field(name="New Balance",   value=format_amount(new_bal),      inline=True)
    embed.add_field(name="Paid By",       value=interaction.user.mention,    inline=True)
    embed.set_footer(text=now_ts())
    _brand_embed(embed)
    await interaction.response.send_message(embed=embed)
    await send_finance_log(embed)

    try:
        dm_e = discord.Embed(
            title="💸  You've Been Paid!",
            color=C_WIN,
            description=(
                f"**{interaction.user}** just paid your weekly staff bonus!\n\n"
                f"**Coins you added this period:** {format_amount(total_added)}\n"
                f"**Your 10% bonus:** +{format_amount(bonus)} 💎\n"
                f"**New balance:** {format_amount(new_bal)} 💎\n\n"
                f"Keep up the great work! 🎉"
            )
        )
        _brand_embed(dm_e)
        await staff_member.send(embed=dm_e)
    except Exception:
        pass  # DMs may be disabled

@bot.tree.command(name="setbalance", description="[Admin] Update a user's account details.")
@app_commands.describe(user="Target user", amount="New balance e.g. 5M")
@admin_only()
async def cmd_setbalance(interaction: discord.Interaction, user: discord.Member, amount: str):
    amt = parse_amount(amount)
    if amt is None or amt < 0:
        await interaction.response.send_message("❌ Invalid amount.", ephemeral=True)
        return

    conn = await get_conn()
    try:
        await ensure_user(conn, user)
        old_bal = (await get_user(conn, user.id))["balance"]
        await set_balance_exact(conn, user.id, amt)
        await log_transaction(conn, user.id, "setbalance", amt, f"by {interaction.user.id}")
    finally:
        await release_conn(conn)

    embed = discord.Embed(title="✅ Balance Set", color=C_GOLD)
    embed.add_field(name="User",        value=user.mention,           inline=True)
    embed.add_field(name="Old Balance", value=format_amount(old_bal), inline=True)
    embed.add_field(name="New Balance", value=format_amount(amt),     inline=True)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed)
    await send_finance_log(embed)

@bot.tree.command(name="checkbalance", description="[Admin] View a user's raw balance.")
@app_commands.describe(user="Target user")
@admin_only()
async def cmd_checkbalance(interaction: discord.Interaction, user: discord.Member):
    conn = await get_conn()
    try:
        await ensure_user(conn, user)
        row = await get_user(conn, user.id)
    finally:
        await release_conn(conn)

    if not row:
        await interaction.response.send_message("❌ Could not load user data.", ephemeral=True)
        return

    embed = discord.Embed(title="🔍 Raw Balance Check", color=C_GOLD)
    embed.add_field(name="User",      value=f"{user} (`{user.id}`)",      inline=False)
    embed.add_field(name="Balance",   value=f"`{row['balance']}`",         inline=True)
    embed.add_field(name="Formatted", value=format_amount(row["balance"]), inline=True)
    embed.add_field(name="Wagered",   value=format_amount(row["wagered"]), inline=True)
    embed.add_field(name="Wins",      value=str(row["wins"]),              inline=True)
    embed.add_field(name="Losses",    value=str(row["losses"]),            inline=True)
    embed.add_field(name="Streak",    value=str(row["streak"]),            inline=True)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed, ephemeral=True)

@bot.tree.command(name="admintip", description="[Admin] Process a house transaction.")
@app_commands.describe(user="Target user", amount="Amount e.g. 5M")
@admin_only()
async def cmd_admintip(interaction: discord.Interaction, user: discord.Member, amount: str):
    amt = parse_amount(amount)
    if not amt or amt <= 0:
        await interaction.response.send_message("❌ Invalid amount.", ephemeral=True)
        return

    conn = await get_conn()
    try:
        await ensure_user(conn, user)
        await update_balance(conn, user.id, amt)
        new_bal = (await get_user(conn, user.id))["balance"]
        await log_transaction(conn, user.id, "admin_tip", amt, f"by {interaction.user.id}")
        row = await get_user(conn, user.id)
        if row and interaction.guild:
            member = interaction.guild.get_member(user.id)
            if member:
                await update_user_rank(member, row["wagered"])
    finally:
        await release_conn(conn)

    embed = discord.Embed(title="💸 Admin Tip Sent", color=C_WIN)
    embed.add_field(name="Recipient",   value=user.mention,             inline=True)
    embed.add_field(name="Amount",      value=format_amount(amt),       inline=True)
    embed.add_field(name="New Balance", value=format_amount(new_bal),   inline=True)
    embed.add_field(name="Admin",       value=interaction.user.mention, inline=True)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed)
    try:
        await user.send(embed=discord.Embed(
            title="🎁 You received a tip!",
            description=f"An admin gifted you **{format_amount(amt)}**!\
Balance: **{format_amount(new_bal)}**",
            color=C_WIN
        ))
    except Exception:
        pass
    await send_finance_log(embed)

@bot.tree.command(name="announce", description="[Admin] Post an announcement to a channel.")
@app_commands.describe(
    channel="Channel to send the announcement to",
    title="Title of the announcement",
    message="Main message body",
    color="Embed color: green, red, blue, gold, purple (default: gold)",
    ping="Role or @everyone to ping (optional)"
)
@admin_only()
async def cmd_announce(
    interaction: discord.Interaction,
    channel: discord.TextChannel,
    title: str,
    message: str,
    color: str = "gold",
    ping: Optional[discord.Role] = None
):
    color_map = {
        "green":  C_WIN,
        "red":    C_LOSS,
        "blue":   C_BLUE,
        "gold":   C_GOLD,
        "purple": 0x9B59B6,
    }
    embed_color = color_map.get(color.lower(), C_GOLD)

    embed = discord.Embed(title=f"📣 {title}", description=message, color=embed_color)
    embed.set_footer(text=f"Announced by {interaction.user.display_name} • {now_ts()}")
    embed.set_thumbnail(url=interaction.guild.icon.url if interaction.guild and interaction.guild.icon else None)

    try:
        ping_str = ""
        if ping:
            ping_str = f"{ping.mention} " if ping.name != "@everyone" else "@everyone "

        await channel.send(content=ping_str if ping_str else None, embed=embed)
        await interaction.response.send_message(
            f"✅ Announcement sent to {channel.mention}!", ephemeral=True)
    except discord.Forbidden:
        await interaction.response.send_message(
            f"❌ No permission to send in {channel.mention}.", ephemeral=True)
        return

    log_e = discord.Embed(title="📣 Announcement Sent", color=embed_color)
    log_e.add_field(name="Admin",   value=interaction.user.mention, inline=True)
    log_e.add_field(name="Channel", value=channel.mention,          inline=True)
    log_e.add_field(name="Title",   value=title,                    inline=True)
    log_e.add_field(name="Ping",    value=ping.mention if ping else "None", inline=True)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

@bot.tree.command(name="dmannouncement", description="[Admin] Send a DM announcement to every member in the server.")
@app_commands.describe(
    title="Title of the announcement",
    message="Main message body",
    color="Embed color: green, red, blue, gold, purple (default: gold)",
    mention="Mention each user in their DM? (yes/no, default: yes)"
)
@admin_only()
async def cmd_dmannouncement(
    interaction: discord.Interaction,
    title: str,
    message: str,
    color: str = "gold",
    mention: str = "yes"
):
    await interaction.response.defer(ephemeral=True)

    color_map = {
        "green":  C_WIN,
        "red":    C_LOSS,
        "blue":   C_BLUE,
        "gold":   C_GOLD,
        "purple": 0x9B59B6,
    }
    embed_color = color_map.get(color.lower(), C_GOLD)
    embed = discord.Embed(title=f"📣 {title}", description=message, color=embed_color)
    embed.set_footer(text=f"bloxysab  ·  {now_ts()}")
    if interaction.guild and interaction.guild.icon:
        embed.set_thumbnail(url=interaction.guild.icon.url)

    guild = interaction.guild
    if not guild:
        await interaction.followup.send("❌ Must be used in a server.", ephemeral=True)
        return

    members = [m for m in guild.members if not m.bot]
    total    = len(members)
    sent     = 0
    failed   = 0
    skipped  = 0

    await interaction.followup.send(
        f"📤 Sending DM announcement to **{total}** members... This may take a while.",
        ephemeral=True
    )

    for member in members:
        try:
            include_mention = mention.lower().strip() in ("yes", "y", "1", "true")
            desc = f"{member.mention}\n\n{embed.description}" if include_mention else embed.description
            personal_embed = discord.Embed(title=embed.title, description=desc, color=embed.color)
            personal_embed.set_footer(text=embed.footer.text if embed.footer else "")
            if embed.thumbnail:
                personal_embed.set_thumbnail(url=embed.thumbnail.url)
            await member.send(embed=personal_embed)
            sent += 1
        except discord.Forbidden:
            skipped += 1   # DMs closed
        except discord.HTTPException as e:
            if e.status == 429:
                await asyncio.sleep(float(e.retry_after) + 0.5)
                try:
                    await member.send(embed=personal_embed)
                    sent += 1
                except Exception:
                    failed += 1
            else:
                failed += 1
        except Exception:
            failed += 1
        await asyncio.sleep(1.2)

    summary = discord.Embed(
        title="✅ DM Announcement Complete",
        color=C_WIN
    )
    summary.add_field(name="✅ Sent",    value=str(sent),    inline=True)
    summary.add_field(name="🔕 Skipped", value=str(skipped), inline=True)
    summary.add_field(name="❌ Failed",  value=str(failed),  inline=True)
    summary.add_field(name="📊 Total",   value=str(total),   inline=True)
    summary.add_field(name="📌 Title",   value=title,        inline=False)
    summary.set_footer(text=f"Sent by {interaction.user.display_name} • {now_ts()}")
    await interaction.followup.send(embed=summary, ephemeral=True)

    log_e = discord.Embed(title="📣 DM Announcement Sent", color=embed_color)
    log_e.add_field(name="Admin",   value=interaction.user.mention,    inline=True)
    log_e.add_field(name="Title",   value=title,                       inline=True)
    log_e.add_field(name="Ping",    value="Yes" if mention.lower().strip() in ("yes", "y", "1", "true") else "No", inline=True)
    log_e.add_field(name="Sent",    value=f"{sent}/{total}",            inline=True)
    log_e.add_field(name="Skipped", value=str(skipped),                 inline=True)
    log_e.add_field(name="Failed",  value=str(failed),                  inline=True)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

@bot.tree.command(name="assignstaff", description="[Admin] Give a user the Moderator role.")
@app_commands.describe(user="User to promote to Moderator")
@admin_only()
async def cmd_assignstaff(interaction: discord.Interaction, user: discord.Member):
    if not interaction.guild:
        await interaction.response.send_message("❌ Must be used in a server.", ephemeral=True)
        return

    staff_role = await ensure_staff_role(interaction.guild)
    if not staff_role:
        await interaction.response.send_message(
            "❌ Could not find or create the Moderator role. Check bot permissions.", ephemeral=True)
        return

    if staff_role in user.roles:
        await interaction.response.send_message(
            f"⚠️ {user.mention} already has the **{STAFF_ROLE_NAME}** role.", ephemeral=True)
        return

    try:
        await user.add_roles(staff_role, reason=f"Assigned by admin {interaction.user}")
    except discord.Forbidden:
        await interaction.response.send_message(
            "❌ Bot lacks permission to assign roles. Make sure the bot's role is above Moderator.", ephemeral=True)
        return

    embed = discord.Embed(
        title="🎖️ Staff Assigned",
        description=f"{user.mention} has been given the **{STAFF_ROLE_NAME}** role.",
        color=C_BLUE
    )
    embed.add_field(name="Assigned By", value=interaction.user.mention, inline=True)
    embed.add_field(name="User",        value=f"{user} (`{user.id}`)",  inline=True)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed)

    try:
        await user.send(embed=discord.Embed(
            title="🎖️ You've been made Moderator!",
            description=f"You were assigned the **{STAFF_ROLE_NAME}** role in **{interaction.guild.name}** by {interaction.user.mention}.",
            color=C_BLUE
        ))
    except Exception:
        pass  # DMs disabled — not a hard failure

    log_e = discord.Embed(title="🎖️ Staff Role Assigned", color=C_BLUE)
    log_e.add_field(name="Admin",  value=interaction.user.mention, inline=True)
    log_e.add_field(name="User",   value=user.mention,             inline=True)
    log_e.set_footer(text=now_ts())
    await send_log(log_e)

@bot.tree.command(name="removestaff", description="[Admin] Remove the Moderator role from a user.")
@app_commands.describe(user="User to remove from Moderator")
@admin_only()
async def cmd_removestaff(interaction: discord.Interaction, user: discord.Member):
    if not interaction.guild:
        await interaction.response.send_message("❌ Must be used in a server.", ephemeral=True)
        return

    staff_role = discord.utils.get(interaction.guild.roles, name=STAFF_ROLE_NAME)
    if not staff_role:
        await interaction.response.send_message(
            f"❌ No **{STAFF_ROLE_NAME}** role found in this server.", ephemeral=True)
        return

    if staff_role not in user.roles:
        await interaction.response.send_message(
            f"⚠️ {user.mention} doesn't have the **{STAFF_ROLE_NAME}** role.", ephemeral=True)
        return

    try:
        await user.remove_roles(staff_role, reason=f"Removed by admin {interaction.user}")
    except discord.Forbidden:
        await interaction.response.send_message(
            "❌ Bot lacks permission to remove roles.", ephemeral=True)
        return

    embed = discord.Embed(
        title="🚫 Staff Removed",
        description=f"{user.mention} has had the **{STAFF_ROLE_NAME}** role removed.",
        color=C_LOSS
    )
    embed.add_field(name="Removed By", value=interaction.user.mention, inline=True)
    embed.add_field(name="User",       value=f"{user} (`{user.id}`)",  inline=True)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed)

    try:
        await user.send(embed=discord.Embed(
            title="🚫 Moderator Role Removed",
            description=f"Your **{STAFF_ROLE_NAME}** role in **{interaction.guild.name}** was removed by {interaction.user.mention}.",
            color=C_LOSS
        ))
    except Exception:
        pass

    log_e = discord.Embed(title="🚫 Staff Role Removed", color=C_LOSS)
    log_e.add_field(name="Admin",  value=interaction.user.mention, inline=True)
    log_e.add_field(name="User",   value=user.mention,             inline=True)
    log_e.set_footer(text=now_ts())
    await send_log(log_e)

@bot.tree.command(name="liststaff", description="[Admin] List all current Moderator members.")
@admin_only()
async def cmd_liststaff(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("❌ Must be used in a server.", ephemeral=True)
        return

    staff_role = discord.utils.get(interaction.guild.roles, name=STAFF_ROLE_NAME)
    if not staff_role:
        await interaction.response.send_message(
            f"❌ No **{STAFF_ROLE_NAME}** role found. Use `/assignstaff` to create it automatically.", ephemeral=True)
        return

    members = [m for m in interaction.guild.members if staff_role in m.roles]
    if not members:
        await interaction.response.send_message(
            f"📋 No members currently have the **{STAFF_ROLE_NAME}** role.", ephemeral=True)
        return

    lines = [f"`{i+1}.` {m.mention} — `{m.id}`" for i, m in enumerate(members)]
    embed = discord.Embed(
        title=f"💰 Moderators ({len(members)})",
        description="\
".join(lines),
        color=C_BLUE
    )
    embed.set_footer(text=f"Use /assignstaff or /removestaff to manage • {now_ts()}")
    await interaction.response.send_message(embed=embed, ephemeral=True)

@bot.tree.command(name="resetdatabase", description="[Admin] ⚠️ DANGER — Wipe ALL data.")
@admin_only()
async def cmd_resetdatabase(interaction: discord.Interaction):
    embed = discord.Embed(
        title="⚠️ DANGER: Reset Database",
        description="This will **permanently delete ALL** user data, stock, and transactions.\
\
**This CANNOT be undone.**",
        color=C_LOSS
    )
    await interaction.response.send_message(embed=embed, view=ResetConfirmView(interaction.user.id), ephemeral=True)

@bot.tree.command(name="verifybalance", description="[Admin] Check for balance issues.")
@admin_only()
async def cmd_verifybalance(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    conn = await get_conn()
    try:
        neg   = await conn.fetchval("SELECT COUNT(*) FROM users WHERE balance<0")
        total = await conn.fetchval("SELECT COALESCE(SUM(balance),0) FROM users") or 0
        users = await conn.fetchval("SELECT COUNT(*) FROM users")
    finally:
        await release_conn(conn)

    ok    = neg == 0
    embed = discord.Embed(title="🔍 Balance Verification", color=C_WIN if ok else C_LOSS)
    embed.add_field(name="Negative Balances", value=str(neg),              inline=True)
    embed.add_field(name="Total Balance Sum",  value=format_amount(total), inline=True)
    embed.add_field(name="Total Users",        value=str(users),           inline=True)
    embed.add_field(name="Status",             value="✅ All good!" if ok else "❌ Issues found!", inline=False)
    embed.set_footer(text=now_ts())
    await interaction.followup.send(embed=embed, ephemeral=True)



@bot.tree.command(name="resetstats", description="[Admin] Reset a user's win/loss/streak.")
@app_commands.describe(user="Target user")
@admin_only()
async def cmd_resetstats(interaction: discord.Interaction, user: discord.Member):
    conn = await get_conn()
    try:
        await ensure_user(conn, user)
        await conn.execute(
            "UPDATE users SET wins=0, losses=0, streak=0, max_streak=0 WHERE user_id=$1",
            str(user.id)
        )
    finally:
        await release_conn(conn)

    embed = discord.Embed(title="✅ Stats Reset", description=f"Stats for {user.mention} reset.", color=C_GOLD)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed)

@bot.tree.command(name="audit", description="[Admin] Full log of every coin an admin has credited.")
@app_commands.describe(admin="Admin to audit (leave empty to see all admins summary)")
@admin_only()
async def cmd_audit(interaction: discord.Interaction, admin: Optional[discord.Member] = None):
    await interaction.response.defer(ephemeral=True)
    conn = await get_conn()
    try:
        if admin:
            rows = await conn.fetch(
                """SELECT t.user_id, t.amount, t.note, t.ts, u.username
                   FROM transactions t
                   LEFT JOIN users u ON u.user_id = t.user_id
                   WHERE t.action = 'addcoins' AND t.note LIKE $1
                   ORDER BY t.id DESC LIMIT 50""",
                f"by {admin.id}%"
            )
            ab_row = await conn.fetchrow(
                "SELECT insurance, used FROM admin_balances WHERE admin_id=$1",
                str(admin.id)
            )
        else:
            rows = await conn.fetch(
                """SELECT note, SUM(amount) as total, COUNT(*) as count
                   FROM transactions WHERE action='addcoins' AND note LIKE 'by %'
                   GROUP BY note ORDER BY total DESC"""
            )
            ab_row = None
    finally:
        await release_conn(conn)

    if admin:
        embed = discord.Embed(
            title=f"🔍 Audit — {admin.display_name}",
            color=C_GOLD
        )
        if ab_row:
            embed.add_field(name="🛡️ Insurance",  value=format_amount(ab_row["insurance"]), inline=True)
            embed.add_field(name="📤 Used",        value=format_amount(ab_row["used"]),      inline=True)
            embed.add_field(name="✅ Remaining",    value=format_amount(max(0, ab_row["insurance"] - ab_row["used"])), inline=True)

        total_credited = sum(r["amount"] for r in rows)
        embed.add_field(name="💎 Total Credited", value=format_amount(total_credited), inline=True)
        embed.add_field(name="🔢 Total Txns",     value=str(len(rows)),                inline=True)

        if rows:
            log_lines = "\n".join(
                f"`{r['ts'][:16]}` → <@{r['user_id']}> (`{r['username'] or '?'}`) **+{format_amount(r['amount'])}**"
                for r in rows[:20]
            )
            embed.add_field(name=f"Last {min(20,len(rows))} Credits", value=log_lines[:1024], inline=False)
        else:
            embed.description = "No credits found for this admin."
    else:
        embed = discord.Embed(
            title="🔍 Audit — All Admins Summary",
            color=C_GOLD
        )
        if rows:
            lines = []
            for r in rows:
                parts = r["note"].split(" ")
                admin_id = parts[1] if len(parts) > 1 else "?"
                lines.append(
                    f"<@{admin_id}> — **{r['count']}** credits totalling **{format_amount(r['total'])}** 💎"
                )
            embed.description = "\n".join(lines) or "No data."
        else:
            embed.description = "No admin credits found."

    try:
        embed.set_footer(text=f"Admin only • {now_ts()}")
        await interaction.followup.send(embed=embed, ephemeral=True)
    except Exception as e:
        print(f"[ERROR] audit: {type(e).__name__}: {e}")
        await interaction.followup.send("⚠️  Something went wrong — try again.", ephemeral=True)

@bot.tree.command(name="adminstats", description="[Admin] bloxysab performance dashboard — house profit, game breakdown, tax collected.")
@admin_only()
async def cmd_adminstats(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    conn = await get_conn()
    try:
        totals = await conn.fetchrow(
            "SELECT COUNT(*) as users, SUM(wagered) as wagered, SUM(total_deposited) as deposited, SUM(balance) as in_circulation FROM users"
        )
        wl = await conn.fetchrow(
            "SELECT SUM(wins) as wins, SUM(losses) as losses FROM users"
        )
        tax_row = await conn.fetchrow(
            "SELECT COALESCE(SUM(ABS(amount)), 0) as total_tax FROM transactions WHERE action LIKE '%_tax'"
        )
        game_rows = await conn.fetch(
            """SELECT action as type, COUNT(*) as count, COALESCE(SUM(ABS(amount)),0) as volume
               FROM transactions
               WHERE action NOT LIKE '%_tax' AND action NOT IN ('addcoins','deposit_ticket','invite_reward','tip','rakeback','rain','wager_requirement_added','wager_requirement_cleared')
               GROUP BY action ORDER BY volume DESC LIMIT 10"""
        )
        tax_rate_row = await conn.fetchrow("SELECT value FROM bot_settings WHERE key='win_tax'")
    finally:
        await release_conn(conn)

    total_wagered   = totals["wagered"] or 0
    total_deposited = totals["deposited"] or 0
    in_circulation  = totals["in_circulation"] or 0
    total_users     = totals["users"] or 0
    total_wins      = wl["wins"] or 0
    total_losses    = wl["losses"] or 0
    total_games     = total_wins + total_losses
    house_edge_pct  = (total_losses / total_games * 100) if total_games > 0 else 0
    total_tax       = int(tax_row["total_tax"]) if tax_row else 0
    tax_rate        = float(tax_rate_row["value"]) if tax_rate_row else 0.12
    house_profit    = total_deposited - in_circulation

    embed = discord.Embed(title="✦  bloxysab — Dashboard", color=C_GOLD)
    embed.add_field(name="👥 Total Users",        value=f"{total_users:,}",                    inline=True)
    embed.add_field(name="💎 In Circulation",     value=format_amount(in_circulation),         inline=True)
    embed.add_field(name="📥 Total Deposited",    value=format_amount(total_deposited),        inline=True)
    embed.add_field(name="🎰 Total Wagered",      value=format_amount(total_wagered),          inline=True)
    embed.add_field(name="✅ Total Wins",          value=f"{total_wins:,}",                    inline=True)
    embed.add_field(name="❌ Total Losses",        value=f"{total_losses:,}",                  inline=True)
    embed.add_field(name="📉 House Win Rate",      value=f"{house_edge_pct:.1f}%",             inline=True)
    embed.add_field(name="💸 Tax Collected",       value=format_amount(total_tax),             inline=True)
    embed.add_field(name="🏦 House Profit Est.",   value=format_amount(max(0, house_profit)),  inline=True)
    embed.add_field(name="📊 Win Tax Rate",        value=f"{tax_rate*100:.0f}%",               inline=True)

    if game_rows:
        game_lines = "\n".join(
            f"`{r['type']:<20}` {r['count']:>5} games  {format_amount(r['volume'])} wagered"
            for r in game_rows
        )
        embed.add_field(name="🎮 Top Games by Volume", value=game_lines, inline=False)

    try:
        embed.set_footer(text=f"Admin only • {now_ts()}")
        await interaction.followup.send(embed=embed, ephemeral=True)
    except Exception as e:
        print(f"[ERROR] adminstats: {type(e).__name__}: {e}")
        await interaction.followup.send("⚠️  Something went wrong — try again.", ephemeral=True)

@bot.tree.command(name="bankroll", description="[Admin] Show total gems in circulation and house financial summary.")
@admin_only()
async def cmd_bankroll(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    conn = await get_conn()
    try:
        totals = await conn.fetchrow(
            "SELECT SUM(balance) as circulation, SUM(total_deposited) as deposited, COUNT(*) as users FROM users"
        )
        tax_row = await conn.fetchrow(
            "SELECT COALESCE(SUM(ABS(amount)), 0) as total FROM transactions WHERE action LIKE '%_tax'"
        )
    finally:
        await release_conn(conn)

    circulation = totals["circulation"] or 0
    deposited   = totals["deposited"] or 0
    users       = totals["users"] or 0
    tax         = int(tax_row["total"]) if tax_row else 0
    profit_est  = deposited - circulation

    embed = discord.Embed(title="Bankroll Overview", color=C_WIN)
    embed.add_field(name="💎 Total In Circulation", value=format_amount(circulation), inline=True)
    embed.add_field(name="📥 Total Deposited",      value=format_amount(deposited),   inline=True)
    embed.add_field(name="👥 Total Players",         value=f"{users:,}",              inline=True)
    embed.add_field(name="💸 Tax Collected",         value=format_amount(tax),         inline=True)
    embed.add_field(name="📈 House Profit Est.",     value=format_amount(max(0, profit_est)), inline=True)

    embed.set_footer(text=f"Admin only • {now_ts()}")
    await interaction.followup.send(embed=embed, ephemeral=True)

_pf_store: dict[str, dict] = {}  # game_id → {server_seed, client_seed, nonce, hash}

def pf_new_game(client_seed: str = "") -> dict:
    """Generate a new provably fair game session. Auto-cleans store if >500 entries."""
    if len(_pf_store) > 500:
        to_delete = [k for k,v in _pf_store.items() if v.get("revealed")][:250]
        for k in to_delete:
            del _pf_store[k]
    server_seed  = secrets.token_hex(32)          # 64 char hex secret
    nonce        = secrets.randbelow(1_000_000)
    if not client_seed:
        client_seed = secrets.token_hex(8)        # random if not provided
    commitment   = hashlib.sha256(server_seed.encode()).hexdigest()
    game_id      = secrets.token_hex(8)
    _pf_store[game_id] = {
        "server_seed":  server_seed,
        "client_seed":  client_seed,
        "nonce":        nonce,
        "commitment":   commitment,
        "game_id":      game_id,
        "revealed":     False,
    }
    return _pf_store[game_id]

def pf_derive_float(server_seed: str, client_seed: str, nonce: int) -> float:
    """Derive a float 0-1 from seeds. This is shown as the 'result source' but not used for actual outcome."""
    msg  = f"{client_seed}:{nonce}".encode()
    h    = hmac.new(server_seed.encode(), msg, hashlib.sha256).hexdigest()
    val  = int(h[:8], 16)
    return val / 0xFFFFFFFF

def pf_reveal(game_id: str, actual_outcome: str) -> dict | None:
    """Reveal the server seed for a completed game."""
    data = _pf_store.get(game_id)
    if not data or data["revealed"]:
        return None
    data["revealed"]       = True
    data["actual_outcome"] = actual_outcome
    data["derived_float"]  = round(pf_derive_float(
        data["server_seed"], data["client_seed"], data["nonce"]
    ), 6)
    return data

def pf_commitment_embed(pf: dict, game_name: str) -> discord.Embed:
    """Embed shown BEFORE the game with the hash commitment."""
    e = discord.Embed(
        title="🔐 Provably Fair",
        description=(
            f"This **{game_name}** game is provably fair.\n"
            f"The outcome was committed to before you played.\n"
            f"After the game, use `/provablyfair` to verify."
        ),
        color=C_DARK
    )
    e.add_field(name="🔒 Server Seed Hash", value=f"`{pf['commitment']}`", inline=False)
    e.add_field(name="🎲 Client Seed",      value=f"`{pf['client_seed']}`", inline=True)
    e.add_field(name="🔢 Nonce",            value=f"`{pf['nonce']}`",       inline=True)
    e.set_footer(text=f"Game ID: {pf['game_id']} • Verify with /provablyfair")
    return e

def pf_reveal_embed(pf: dict, game_name: str) -> discord.Embed:
    """Embed shown AFTER the game revealing the server seed."""
    e = discord.Embed(
        title="🔓 Provably Fair — Result Verified",
        description=(
            f"The server seed has been revealed. You can verify the outcome yourself:\n"
            f"`SHA256(server_seed) == commitment` ✅"
        ),
        color=C_WIN
    )
    e.add_field(name="🔓 Server Seed",      value=f"`{pf['server_seed']}`",  inline=False)
    e.add_field(name="🔒 Commitment Hash",  value=f"`{pf['commitment']}`",   inline=False)
    e.add_field(name="🎲 Client Seed",      value=f"`{pf['client_seed']}`",  inline=True)
    e.add_field(name="🔢 Nonce",            value=f"`{pf['nonce']}`",        inline=True)
    e.add_field(name="📊 Derived Value",    value=f"`{pf['derived_float']}`",inline=True)
    e.add_field(name="🎰 Game",             value=game_name,                 inline=True)
    e.add_field(name="✅ Outcome",           value=pf.get("actual_outcome","—"), inline=True)
    e.set_footer(text=f"Game ID: {pf['game_id']} • Verify: sha256.online")
    return e

@bot.tree.command(name="provablyfair", description="Verify a past game result using its Game ID.")
@app_commands.describe(game_id="The Game ID shown after your game (8 characters)")
async def cmd_provablyfair(interaction: discord.Interaction, game_id: str):
    pf = _pf_store.get(game_id.lower().strip())
    if not pf:
        embed = discord.Embed(
            title="❓ Game Not Found",
            description=(
                f"No game found with ID `{game_id}`.\n\n"
                "**Note:** Game IDs are only stored for the current bot session. "
                "If the bot restarted, old IDs are cleared.\n\n"
                "You can still manually verify any past game:\n"
                "1. Take the **Server Seed** revealed after the game\n"
                "2. Hash it with SHA-256 at [sha256.online](https://emn178.github.io/online-tools/sha256.html)\n"
                "3. Compare it to the **Commitment Hash** shown before the game"
            ),
            color=C_WARN
        )
        await interaction.response.send_message(embed=embed, ephemeral=True)
        return

    if not pf["revealed"]:
        embed = discord.Embed(
            title="⏳ Game In Progress",
            description="This game hasn't finished yet. The server seed will be revealed after it completes.",
            color=C_GOLD
        )
        embed.add_field(name="🔒 Commitment Hash", value=f"`{pf['commitment']}`", inline=False)
        embed.add_field(name="🎲 Client Seed",     value=f"`{pf['client_seed']}`", inline=True)
        embed.add_field(name="🔢 Nonce",           value=f"`{pf['nonce']}`",       inline=True)
        embed.set_footer(text=f"Game ID: {pf['game_id']}")
        await interaction.response.send_message(embed=embed, ephemeral=True)
        return

    name = pf.get("game_name", "bloxysab Game")
    embed = pf_reveal_embed(pf, name)
    embed.description += (
        "\n\n**How to verify yourself:**\n"
        "1. Copy the **Server Seed** above\n"
        "2. Go to [sha256.online](https://emn178.github.io/online-tools/sha256.html)\n"
        "3. Paste the seed and hash it\n"
        "4. It will match the **Commitment Hash** exactly ✅"
    )
    await interaction.response.send_message(embed=embed, ephemeral=True)

@bot.tree.command(name="settax", description="[Admin] Set the win tax percentage on all game profits.")
@app_commands.describe(percent="Tax percentage e.g. 12 for 12%, 0 to disable")
@admin_only()
async def cmd_settax(interaction: discord.Interaction, percent: float):
    if percent < 0 or percent > 50:
        await interaction.response.send_message("❌ Tax must be between 0% and 50%.", ephemeral=True)
        return

    rate = percent / 100
    conn = await get_conn()
    try:
        await conn.execute(
            """INSERT INTO bot_settings (key, value) VALUES ('win_tax', $1)
               ON CONFLICT (key) DO UPDATE SET value = $1""",
            str(rate)
        )
    finally:
        await release_conn(conn)

    embed = discord.Embed(
        title="💸 Win Tax Updated",
        description=(
            f"Win tax set to **{percent:.1f}%**\n\n"
            f"Players now keep **{100-percent:.1f}%** of their profits.\n"
            f"Example: Win 1M profit → taxed **{format_amount(int(1_000_000 * rate))}** → receive **{format_amount(int(1_000_000 * (1-rate)))}**"
        ),
        color=C_GOLD
    )
    embed.set_footer(text=f"Set by {interaction.user} | {now_ts()}")
    await interaction.response.send_message(embed=embed)

    log_e = discord.Embed(title="💸 Win Tax Changed", color=C_GOLD)
    log_e.add_field(name="New Rate", value=f"{percent:.1f}%", inline=True)
    log_e.add_field(name="Set By",   value=interaction.user.mention, inline=True)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

@bot.tree.command(name="test", description="[Admin] Run a diagnostic check on a user session.")
@app_commands.describe(user="Target user", result="Session parameter")
@app_commands.choices(result=[
    app_commands.Choice(name="Win",  value="win"),
    app_commands.Choice(name="Lose", value="lose"),
])
@admin_only()
async def cmd_test(interaction: discord.Interaction, user: discord.Member, result: str):
    _force_result[user.id] = result
    emoji = "✅" if result == "win" else "❌"
    await interaction.response.send_message(
        f"{emoji} {user.mention}'s next game will force **{result.upper()}**. Single use — resets after one game.",
        ephemeral=True
    )

@bot.tree.command(name="admincasebattles", description="[Admin] Adjust internal case battle parameters.")
@app_commands.describe(
    player_luck="Player parameter (0-100)",
    bot_luck="System parameter (0-100)"
)
@admin_only()
async def cmd_admincasebattles(interaction: discord.Interaction, player_luck: int, bot_luck: int):
    global CB_PLAYER_LUCK, CB_BOT_LUCK

    if not (0 <= player_luck <= 100) or not (0 <= bot_luck <= 100):
        await interaction.response.send_message("❌ Values must be 0–100.", ephemeral=True)
        return

    CB_PLAYER_LUCK = player_luck
    CB_BOT_LUCK    = bot_luck

    import json as _json
    conn = await get_conn()
    try:
        await conn.execute(
            "INSERT INTO bot_settings (key, value) VALUES ('cb_nerf_level', $1) "
            "ON CONFLICT (key) DO UPDATE SET value=$1",
            _json.dumps({"player": player_luck, "bot": bot_luck})
        )
    finally:
        await release_conn(conn)

    def _luck_label(v):
        if v <= 10:  return "🔴 Terrible"
        if v <= 30:  return "🟠 Bad"
        if v <= 45:  return "🟡 Below Fair"
        if v <= 55:  return "⚪ Fair"
        if v <= 70:  return "🟢 Good"
        if v <= 90:  return "💚 Great"
        return "⭐ Insane"

    def _bar(v):
        filled = round(v / 10)
        return "█" * filled + "░" * (10 - filled) + f" `{v}/100`"

    embed = discord.Embed(
        title="⚔️ Case Battle RNG Updated",
        color=C_GOLD
    )
    embed.add_field(
        name=f"👤 Player Weight — {_luck_label(player_luck)}",
        value=_bar(player_luck),
        inline=False
    )
    embed.add_field(
        name=f"🤖 Bot Weight — {_luck_label(bot_luck)}",
        value=_bar(bot_luck),
        inline=False
    )
    embed.add_field(
        name="ℹ️ Info",
        value="Controls RNG distribution weight for each side in case battles.",
        inline=False
    )
    embed.set_footer(text=f"Set by {interaction.user} | {now_ts()}")
    await interaction.response.send_message(embed=embed)

    log_e = discord.Embed(title="⚔️ CB RNG Settings Changed", color=C_GOLD)
    log_e.add_field(name="Player Weight", value=f"`{player_luck}`", inline=True)
    log_e.add_field(name="Bot Weight",    value=f"`{bot_luck}`",    inline=True)
    log_e.add_field(name="Set By",      value=interaction.user.mention,                          inline=True)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

@bot.tree.command(name="testconfig", description="[Admin] View current system configuration.")
@admin_only()
async def cmd_edge(interaction: discord.Interaction):
    await interaction.response.send_message(
        embed=discord.Embed(
            title="🎰 Game Settings",
            description="Select a game to view its configuration.",
            color=C_GOLD
        ),
        view=GameConfigSelectView(),
        ephemeral=True
    )

def _edge_embed(game: str) -> discord.Embed:
    """Build the current edge info embed for a given game."""
    e = discord.Embed(title=f"🎰 Game Config — {game}", color=C_GOLD)

    if game == "Coinflip / Dice / War / Baccarat":
        e.description = "Current setting active."
        e.add_field(name="Adjust:", value="Use buttons below ↓", inline=False)

    elif game == "Roulette":
        outcomes = ROULETTE_OUTCOMES
        ev = sum(p * m for _, _, p, m in outcomes)
        edge = round((1 - ev) * 100, 2)
        lines = "\n".join(f"{em} {nm}: prob={p:.4f} pays={m}x" for em, nm, p, m in outcomes)
        e.description = f"**EV = {ev:.4f} → Edge = {edge:.2f}%**\n```\n{lines}\n```"
        e.add_field(name="Adjust:", value="Use buttons below ↓", inline=False)

    elif game == "Mines":
        e.description = "Multiplier per gem = `(safe_prob)⁻¹ × factor`, compounding with depth."
        e.add_field(name="Adjust:", value="Use buttons below ↓", inline=False)

    elif game == "Upgrader":
        e.description = "Real win chance = `(1 / multiplier) × factor`."
        e.add_field(name="Adjust:", value="Use buttons below ↓", inline=False)

    elif game == "Horse Race":
        edge = round((1 - HORSE_PAYOUT / 4) * 100, 2)
        e.description = f"Current payout multiplier: `{HORSE_PAYOUT}x`"
        e.add_field(name="Adjust:", value="Use buttons below ↓", inline=False)

    elif game == "Scratch Card":
        e.description = "Scratch win rate and payout table configuration."
        e.add_field(name="Adjust:", value="Use buttons below ↓", inline=False)

    elif game == "Color Dice":
        edge = 0  # Edge info hidden
        e.description = f"Config loaded."
        e.add_field(name="Adjust:", value="Use buttons below ↓", inline=False)

    elif game == "Blackjack":
        stand_edge = {16: "~2%", 17: "~4%", 18: "~6%", 19: "~8%", 20: "~10%"}
        approx = stand_edge.get(BJ_DEALER_STAND, "?")
        e.description = (
            f"**`BJ_DEALER_STAND = {BJ_DEALER_STAND}`**\n"
            f"Dealer draws until they reach this total.\n"
            f"• **16** = player-friendly\n"
            f"• **17** = standard\n"
            f"• **18** = harder\n"
            f"• **19** = heavy"
        )
        e.add_field(name="Adjust:", value="Use buttons below ↓", inline=False)

    elif game == "Case Battle":
        e.description = "Use /admincasebattles to configure case battle RNG weights."
        e.add_field(name="Adjust:", value="Use buttons below ↓", inline=False)

    e.set_footer(text="Changes apply immediately.")
    return e

EDGE_PRESETS = {
    "1%":  0.01,
    "2%":  0.02,
    "3%":  0.03,
    "4%":  0.04,
    "5%":  0.05,
    "6%":  0.06,
    "8%":  0.08,
    "10%": 0.10,
}

class HouseEdgeGameView(discord.ui.View):
    """Shows edge info for one game + preset buttons to change it."""
    def __init__(self, game: str):
        super().__init__(timeout=120)
        self.game = game
        for label, val in EDGE_PRESETS.items():
            btn = discord.ui.Button(
                label=label, style=discord.ButtonStyle.blurple, custom_id=f"edge_{label}"
            )
            btn.callback = self._make_callback(val, label)
            self.add_item(btn)
        back = discord.ui.Button(label="◀ Back", style=discord.ButtonStyle.grey, row=2)
        back.callback = self._back
        self.add_item(back)

    def _make_callback(self, edge_val: float, label: str):
        async def callback(interaction: discord.Interaction):
            global BOT_HOUSE_WIN, BOT_HOUSE_WIN_CD, HORSE_PAYOUT, ROULETTE_OUTCOMES
            g = self.game

            if g == "Coinflip / Dice / War / Baccarat":
                BOT_HOUSE_WIN = 0.5 + edge_val / 2
                msg = f"Updated. New setting: `{BOT_HOUSE_WIN:.4f}`"

            elif g == "Roulette":
                target_ev = 1 - edge_val
                p = (6 - target_ev) / 8
                pY = max(0.01, 1 - 2 * p)
                ROULETTE_OUTCOMES = [
                    ("🔴", "Red",    round(p,  4), 2.0),
                    ("⚫", "Black",  round(p,  4), 2.0),
                    ("🟡", "Yellow", round(pY, 4), 6.0),
                ]
                actual_ev = sum(pr * m for _, _, pr, m in ROULETTE_OUTCOMES)
                msg = f"Updated. EV={actual_ev:.4f}"

            elif g == "Mines":
                factor = 1 - edge_val
                import types
                def new_factor(mines: int) -> float:
                    return factor
                globals()["mines_dynamic_factor"] = new_factor
                msg = f"Updated. Factor: `{factor:.4f}`"

            elif g == "Upgrader":
                factor = 1 - edge_val
                def new_upgrader_real_chance(mult: float) -> float:
                    return (1.0 / mult) * factor
                globals()["upgrader_real_chance"] = new_upgrader_real_chance
                msg = f"Updated. Factor: `{factor:.4f}`"

            elif g == "Blackjack":
                global BJ_DEALER_STAND
                if edge_val <= 0.02:
                    BJ_DEALER_STAND = 16
                elif edge_val <= 0.04:
                    BJ_DEALER_STAND = 17
                elif edge_val <= 0.06:
                    BJ_DEALER_STAND = 18
                elif edge_val <= 0.08:
                    BJ_DEALER_STAND = 19
                else:
                    BJ_DEALER_STAND = 20
                msg = f"Updated. Dealer stand: `{BJ_DEALER_STAND}`"

            elif g == "Horse Race":
                HORSE_PAYOUT = round(4 * (1 - edge_val), 4)
                globals()["HORSE_PAYOUT"] = HORSE_PAYOUT
                msg = f"Updated. Payout: `{HORSE_PAYOUT}x`"

            elif g == "Scratch Card":
                base_win_rate = 0.2718
                base_edge = 0.04
                new_rate = round(base_win_rate * (base_edge / edge_val), 4) if edge_val else base_win_rate
                new_rate = max(0.01, min(0.99, new_rate))
                import builtins
                globals()["SCRATCH_WIN_RATE"] = new_rate
                msg = f"Updated. Rate: `{new_rate:.4f}`"

            elif g == "Color Dice":
                BOT_HOUSE_WIN_CD = edge_val / 0.5  # back-calculate to get ~edge% overall
                BOT_HOUSE_WIN_CD = round(min(0.99, BOT_HOUSE_WIN_CD), 4)
                globals()["BOT_HOUSE_WIN_CD"] = BOT_HOUSE_WIN_CD
                msg = f"Updated. Setting: `{BOT_HOUSE_WIN_CD}`"

            elif g == "Case Battle":
                global BOT_CB_HOUSE_EDGE
                BOT_CB_HOUSE_EDGE = 0.5 + edge_val / 2
                BOT_CB_HOUSE_EDGE = round(min(0.99, BOT_CB_HOUSE_EDGE), 4)
                globals()["BOT_CB_HOUSE_EDGE"] = BOT_CB_HOUSE_EDGE
                msg = f"Updated. Setting: `{BOT_CB_HOUSE_EDGE}`"

            else:
                msg = "Unknown game."

            embed = _edge_embed(self.game)
            embed.add_field(name="✅ Saved", value=msg, inline=False)
            await interaction.response.edit_message(embed=embed, view=self)
        return callback

    async def _back(self, interaction: discord.Interaction):
        await interaction.response.edit_message(
            embed=discord.Embed(
                title="⚙️ Bot Config",
                description="Select a game configuration below.",
                color=C_GOLD
            ),
            view=GameConfigSelectView()
        )

class GameConfigSelectView(discord.ui.View):
    """Game selector — one button per game."""
    GAMES = [
        ("🪙 Coinflip / Dice / War / Baccarat",  "Coinflip / Dice / War / Baccarat"),
        ("◉  ROULETTE",               "Roulette"),
        ("💣  MINES",                  "Mines"),
        ("⬆️ Upgrader",              "Upgrader"),
        ("🏇  HORSE RACE",             "Horse Race"),
        ("🎫  SCRATCH",           "Scratch Card"),
        ("🎲 Color Dice",             "Color Dice"),
        ("♠️ Blackjack",              "Blackjack"),
        ("⚔️ Case Battle Bot",        "Case Battle"),
    ]

    def __init__(self):
        super().__init__(timeout=120)
        for label, game_id in self.GAMES:
            btn = discord.ui.Button(label=label, style=discord.ButtonStyle.blurple)
            btn.callback = self._make_callback(game_id)
            self.add_item(btn)

    def _make_callback(self, game_id: str):
        async def callback(interaction: discord.Interaction):
            await interaction.response.edit_message(
                embed=_edge_embed(game_id),
                view=HouseEdgeGameView(game_id)
            )
        return callback

@bot.tree.command(name="resetwager", description="[Admin] Reset a user's total wagered to 0.")
@app_commands.describe(user="Target user")
@admin_only()
async def cmd_resetwager(interaction: discord.Interaction, user: discord.Member):
    conn = await get_conn()
    try:
        await ensure_user(conn, user)
        await conn.execute(
            "UPDATE users SET wagered=0 WHERE user_id=$1",
            str(user.id)
        )
        if interaction.guild:
            member = interaction.guild.get_member(user.id)
            if member:
                await update_user_rank(member, 0)
    except Exception as e:
        print(f"[ERROR] resetwager: {type(e).__name__}: {e}")
        await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
        return
    finally:
        await release_conn(conn)

    embed = discord.Embed(title="✅ Wager Reset", description=f"Wagered reset for {user.mention}.", color=C_GOLD)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed)

@bot.tree.command(name="addwager", description="[Admin] Add a wager requirement to a user before they can withdraw.")
@app_commands.describe(user="Target user", amount="Wager requirement amount e.g. 5M, 10M")
@admin_only()
async def cmd_addwager(interaction: discord.Interaction, user: discord.Member, amount: str):
    amt = parse_amount(amount)
    if not amt or amt <= 0:
        await interaction.response.send_message("❌ Invalid amount.", ephemeral=True)
        return

    conn = await get_conn()
    try:
        await ensure_user(conn, user)
        row = await conn.fetchrow(
            "SELECT required_amt, wagered_so_far, req_met FROM wager_requirements WHERE user_id=$1",
            str(user.id)
        )
        if row and not row["req_met"]:
            new_required = row["required_amt"] + amt
            await conn.execute(
                "UPDATE wager_requirements SET required_amt=$1, req_met=FALSE WHERE user_id=$2",
                new_required, str(user.id)
            )
            already = row["wagered_so_far"]
            total_required = new_required
        else:
            await conn.execute(
                """INSERT INTO wager_requirements (user_id, required_amt, wagered_so_far, req_met)
                   VALUES ($1, $2, 0, FALSE)
                   ON CONFLICT (user_id) DO UPDATE SET
                       required_amt   = $2,
                       wagered_so_far = 0,
                       req_met        = FALSE""",
                str(user.id), amt
            )
            already = 0
            total_required = amt

        await log_transaction(conn, user.id, "wager_requirement_added", amt, f"set by {interaction.user.name}")
    finally:
        await release_conn(conn)

    progress = progress_bar(already, total_required)
    embed = discord.Embed(title="Wager Requirement Added", color=C_WARN)
    embed.add_field(name="User",       value=user.mention,                 inline=True)
    embed.add_field(name="Added",      value=format_amount(amt),           inline=True)
    embed.add_field(name="Total Req",  value=format_amount(total_required), inline=True)
    embed.add_field(name="Progress",   value=f"`{progress}` {format_amount(already)}/{format_amount(total_required)}", inline=False)
    embed.set_footer(text=f"Set by {interaction.user.name} • {now_ts()}")
    await interaction.response.send_message(embed=embed)

    await send_finance_log(embed)

@bot.tree.command(name="checkwager", description="[Admin] Check a user's current wager requirement status.")
@app_commands.describe(user="Target user")
@admin_only()
async def cmd_checkwager(interaction: discord.Interaction, user: discord.Member):
    conn = await get_conn()
    try:
        await ensure_user(conn, user)
        row = await conn.fetchrow(
            "SELECT required_amt, wagered_so_far, req_met FROM wager_requirements WHERE user_id=$1",
            str(user.id)
        )
    except Exception as e:
        print(f"[ERROR] checkwager: {type(e).__name__}: {e}")
        await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
        return
    finally:
        await release_conn(conn)

    if not row or row["req_met"] or not row["required_amt"]:
        embed = discord.Embed(
            title="✅ No Active Wager Requirement",
            description=f"{user.mention} has no pending wager requirement.",
            color=C_WIN
        )
        await interaction.response.send_message(embed=embed, ephemeral=True)
        return

    required = row["required_amt"]
    wagered  = row["wagered_so_far"]
    remaining = max(0, required - wagered)
    pct = min(100, int(wagered / required * 100)) if required else 100
    bar = progress_bar(wagered, required)

    embed = discord.Embed(color=C_WARN)
    embed.set_thumbnail(url=await get_avatar(user))
    embed.add_field(name="User",      value=user.mention,              inline=True)
    embed.add_field(name="Required",  value=format_amount(required),   inline=True)
    embed.add_field(name="Wagered",   value=format_amount(wagered),    inline=True)
    embed.add_field(name="Remaining", value=format_amount(remaining),  inline=True)
    embed.add_field(name="Complete",  value=f"{pct}%",                 inline=True)
    embed.add_field(name="Progress",  value=f"`{bar}`",                inline=False)
    embed.set_footer(text=now_ts())
    await interaction.response.send_message(embed=embed, ephemeral=True)

@bot.tree.command(name="clearwager", description="[Admin] Clear/remove a user's wager requirement.")
@app_commands.describe(user="Target user")
@admin_only()
async def cmd_clearwager(interaction: discord.Interaction, user: discord.Member):
    conn = await get_conn()
    try:
        await conn.execute(
            "UPDATE wager_requirements SET req_met=TRUE WHERE user_id=$1",
            str(user.id)
        )
        await log_transaction(conn, user.id, "wager_requirement_cleared", 0, f"cleared by {interaction.user.name}")
    except Exception as e:
        print(f"[ERROR] clearwager: {type(e).__name__}: {e}")
        await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
        return
    finally:
        await release_conn(conn)

    embed = discord.Embed(
        title="✅ Wager Requirement Cleared",
        description=f"Wager requirement for {user.mention} has been removed.",
        color=C_WIN
    )
    embed.set_footer(text=f"Cleared by {interaction.user.name} • {now_ts()}")
    await interaction.response.send_message(embed=embed)

@bot.tree.command(name="userlogs", description="[Admin] View last 20 transactions for a user.")
@app_commands.describe(user="Target user")
@admin_only()
async def cmd_userlogs(interaction: discord.Interaction, user: discord.Member):
    conn = await get_conn()
    try:
        rows = await conn.fetch(
            "SELECT action, amount, note, ts FROM transactions WHERE user_id=$1 ORDER BY id DESC LIMIT 20",
            str(user.id)
        )
    except Exception as e:
        print(f"[ERROR] userlogs: {type(e).__name__}: {e}")
        await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
        return
    finally:
        await release_conn(conn)

    if not rows:
        await interaction.response.send_message("📋 No transactions found.", ephemeral=True)
        return

    lines = [
        f"`{r['ts'][:16]}` **{r['action']}** {'+' if r['amount'] >= 0 else ''}{format_amount(r['amount'])}"
        for r in rows
    ]
    embed = discord.Embed(title=f"📋 Logs for {user.display_name}", description="\
".join(lines), color=C_GOLD)
    embed.set_footer(text=f"Last 20 | {now_ts()}")
    await interaction.response.send_message(embed=embed, ephemeral=True)

@bot.tree.command(name="createranks", description="[Admin] Create all rank roles and the staff role manually.")
@admin_only()
async def cmd_createranks(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("❌ Must be used in a server.", ephemeral=True)
        return
    await interaction.response.defer(ephemeral=True)
    created = []

    for low, high, emoji, name, color in RANK_DATA:
        role_name = f"{emoji} {name}"
        existing = discord.utils.get(interaction.guild.roles, name=role_name)
        if not existing:
            try:
                await interaction.guild.create_role(
                    name=role_name,
                    color=discord.Color(color),
                    hoist=True,
                    mentionable=False,
                    reason="Manual rank role creation"
                )
                created.append(role_name)
            except Exception as e:
                print(f"[ERROR] {type(e).__name__}: {e}")
                await interaction.followup.send(f"❌ Failed to create {role_name}: {e}", ephemeral=True)
                return

    staff_existing = discord.utils.get(interaction.guild.roles, name=STAFF_ROLE_NAME)
    if not staff_existing:
        result = await ensure_staff_role(interaction.guild)
        if result:
            created.append(STAFF_ROLE_NAME)
        else:
            await interaction.followup.send(f"⚠️ Rank roles done but failed to create **{STAFF_ROLE_NAME}**.", ephemeral=True)
            return

    if created:
        await interaction.followup.send(f"✅ Created roles: {', '.join(created)}", ephemeral=True)
    else:
        await interaction.followup.send("✅ All rank and staff roles already exist!", ephemeral=True)

@bot.tree.interaction_check
async def global_link_check(interaction: discord.Interaction) -> bool:
    """Block every slash command (except /link and admin cmds) until Roblox is linked."""
    cmd_name = interaction.command.name if interaction.command else ""
    exempt = {"link", "sync", "clearsync", "resetdatabase", "disable"}
    if cmd_name in exempt:
        return True
    if interaction.guild and hasattr(interaction.user, "roles"):
        if any(r.name in (ADMIN_ROLE_NAME, OWNER_ROLE_NAME) for r in interaction.user.roles):
            return True
    conn = None
    try:
        conn = await get_conn()
        row = await conn.fetchrow(
            "SELECT roblox_username FROM roblox_links WHERE user_id=$1",
            str(interaction.user.id)
        )
    except Exception:
        row = None
    finally:
        if conn:
            await release_conn(conn)
    if row:
        return True
    e = discord.Embed(
        title="🔗  Link Required",
        description=(
            "You must link your **Roblox account** before using any bloxysab commands.\n\n"
            "> Use `/link <username>` to connect your Roblox account.\n"
            "> Your Roblox avatar will appear on all game embeds once linked!"
        ),
        color=C_LOSS
    )
    _brand_embed(e)
    try:
        await interaction.response.send_message(embed=e, ephemeral=True)
    except Exception:
        pass
    return False

@bot.tree.error
async def on_app_command_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    if isinstance(error, app_commands.CheckFailure):
        return

    original = getattr(error, "original", error)

    import traceback
    tb = traceback.format_exc()
    print(f"[ERROR] /{getattr(interaction.command, 'name', '?')}: {type(original).__name__}: {original}")
    print(tb)

    if isinstance(original, RuntimeError) and "Database" in str(original):
        msg = "⏳ The bot is still starting up. Please wait a moment and try again."
    elif isinstance(original, asyncio.TimeoutError):
        msg = "⏳ The request timed out. Please try again."
    else:
        msg = f"❌ Error in `/{getattr(interaction.command, 'name', '?')}`: `{type(original).__name__}: {str(original)[:200]}`"

    try:
        if interaction.response.is_done():
            await interaction.followup.send(msg, ephemeral=True)
        else:
            await interaction.response.send_message(msg, ephemeral=True)
    except Exception as _err:
        print(f"[ERROR] Failed to send error message: {_err}")

VIP_MIN_BALANCE   = 70_000_000   # 70M gems required to create/keep a VIP room
VIP_WARN_MINUTES  = 5               # minutes before deletion after warning
VIP_CATEGORY_NAME = "👑 VIP"        # Same category as the VIP lounge — rooms created here too

_vip_warn_tasks: dict[int, asyncio.Task] = {}

async def get_vip_channel(guild: discord.Guild, owner_id: int) -> Optional[discord.TextChannel]:
    """Find the VIP channel owned by this user."""
    return discord.utils.find(
        lambda c: isinstance(c, discord.TextChannel) and c.topic == f"vip:{owner_id}",
        guild.channels
    )

async def vip_delete_channel(channel: discord.TextChannel, owner_id: int, reason: str):
    """Delete a VIP channel and clean up warning task."""
    task = _vip_warn_tasks.pop(owner_id, None)
    if task and not task.done():
        task.cancel()
    try:
        await channel.delete(reason=reason)
    except Exception as _err:
        print(f"[ERROR] Failed to send error message: {_err}")
        pass

async def vip_warn_then_delete(channel: discord.TextChannel, owner_id: int, owner_mention: str):
    """Send warning, wait VIP_WARN_MINUTES, then delete if balance still low."""
    try:
        warn_embed = discord.Embed(
            title="⚠️  VIP WARNING",
            description=(
                f"{owner_mention} Your balance has dropped below **{format_amount(VIP_MIN_BALANCE)}** 💎.\
\
"
                f"You have **{VIP_WARN_MINUTES} minutes** to bring your balance back up, "
                f"or this VIP room will be **automatically deleted**."
            ),
            color=C_GOLD
        )
        warn_embed.set_footer(text=f"Room deletes in {VIP_WARN_MINUTES} minutes if balance stays low")
        await channel.send(embed=warn_embed)
        await asyncio.sleep(VIP_WARN_MINUTES * 60)

        conn = await get_conn()
        try:
            row = await get_user(conn, owner_id)
            balance = row["balance"] if row else 0
        finally:
            await release_conn(conn)

        if balance < VIP_MIN_BALANCE:
            del_embed = discord.Embed(
                title="🔒 VIP Room Deleted",
                description=(
                    f"Balance remained below **{format_amount(VIP_MIN_BALANCE)}** 💎.\
"
                    f"This VIP room has been automatically deleted."
                ),
                color=C_LOSS
            )
            try:
                await channel.send(embed=del_embed)
                await asyncio.sleep(3)
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
            await vip_delete_channel(channel, owner_id, "Balance dropped below VIP minimum")
        else:
            _vip_warn_tasks.pop(owner_id, None)
            try:
                await channel.send(embed=discord.Embed(
                    title="✅ VIP Room Saved",
                    description=f"Balance restored above **{format_amount(VIP_MIN_BALANCE)}** 💎. Room is safe!",
                    color=C_WIN
                ))
            except Exception as e:

                print(f"[ERROR] {type(e).__name__}: {e}")
                pass
    except asyncio.CancelledError:
        pass  # Warning was cancelled (balance recovered or room deleted manually)

async def check_vip_balance(user_id: int, guild: discord.Guild | None):
    """Called after every game result. Triggers warning if balance drops below VIP min."""
    if guild is None:
        return
    channel = await get_vip_channel(guild, user_id)
    if channel is None:
        return  # User has no VIP room

    conn = await get_conn()
    try:
        row = await get_user(conn, user_id)
        balance = row["balance"] if row else 0
    finally:
        await release_conn(conn)

    if balance < VIP_MIN_BALANCE:
        if user_id not in _vip_warn_tasks or _vip_warn_tasks[user_id].done():
            member = guild.get_member(user_id)
            mention = member.mention if member else f"<@{user_id}>"
            task = asyncio.create_task(vip_warn_then_delete(channel, user_id, mention))
            _vip_warn_tasks[user_id] = task
    else:
        task = _vip_warn_tasks.pop(user_id, None)
        if task and not task.done():
            task.cancel()

@bot.tree.command(name="createviproom", description="Create your own private VIP room (requires 70M+ balance).")
async def cmd_createviproom(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("❌ Server only.", ephemeral=True)
        return

    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        row = await get_user(conn, interaction.user.id)
        balance = row["balance"] if row else 0
    finally:
        await release_conn(conn)

    if balance < VIP_MIN_BALANCE:
        await interaction.response.send_message(
            f"❌ You need at least **{format_amount(VIP_MIN_BALANCE)}** 💎 to create a VIP room.\
"
            f"Your balance: **{format_amount(balance)}** 💎",
            ephemeral=True)
        return

    existing = await get_vip_channel(interaction.guild, interaction.user.id)
    if existing:
        await interaction.response.send_message(
            f"❌ You already have a VIP room: {existing.mention}", ephemeral=True)
        return

    await interaction.response.defer(ephemeral=True)

    category = discord.utils.get(interaction.guild.categories, name=VIP_CATEGORY_NAME)
    if not category:
        try:
            category = await interaction.guild.create_category(
                VIP_CATEGORY_NAME,
                overwrites={
                    interaction.guild.default_role: discord.PermissionOverwrite(read_messages=False)
                }
            )
        except discord.Forbidden:
            await interaction.followup.send("❌ Bot lacks permission to create categories.", ephemeral=True)
            return

    overwrites = {
        interaction.guild.default_role: discord.PermissionOverwrite(read_messages=False),
        interaction.user:               discord.PermissionOverwrite(read_messages=True, send_messages=True),
        interaction.guild.me:           discord.PermissionOverwrite(
            read_messages=True, send_messages=True, manage_channels=True, manage_permissions=True),
    }
    admin_role = discord.utils.get(interaction.guild.roles, name=ADMIN_ROLE_NAME)
    if admin_role:
        overwrites[admin_role] = discord.PermissionOverwrite(read_messages=True, send_messages=True)

    try:
        channel = await interaction.guild.create_text_channel(
            name=f"👑・{interaction.user.display_name.lower().replace(' ', '-')}-vip",
            overwrites=overwrites,
            category=category,
            topic=f"vip:{interaction.user.id}"  # used to identify owner
        )
    except discord.Forbidden:
        await interaction.followup.send("❌ Bot lacks permission to create channels.", ephemeral=True)
        return

    welcome = discord.Embed(
        title="VIP Room Created",
        description=(
            f"Welcome to your private VIP room, {interaction.user.mention}!\n\n"
            f"**This room is for you only** \U0001f512\n\n"
            f"**Rules:**\n"
            f"\u2022 Only you can see and use this room\n"
            f"\u2022 Keep your balance above **{format_amount(VIP_MIN_BALANCE)}** \U0001f48e\n"
            f"\u2022 Balance drops below threshold \u2192 **{VIP_WARN_MINUTES} min warning** \u2192 auto delete\n"
            f"\u2022 Use `/deleteviproom` to remove it yourself"
        ),
        color=C_VIP
    )
    welcome.set_footer(text=f"Owner: {interaction.user.display_name} \u2022 Solo VIP Room")
    await channel.send(embed=welcome)
    await interaction.followup.send(f"\u2705 Your private solo VIP room has been created: {channel.mention}", ephemeral=True)

@bot.tree.command(name="deleteviproom", description="Delete your VIP room.")
async def cmd_deleteviproom(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("❌ Server only.", ephemeral=True)
        return

    channel = await get_vip_channel(interaction.guild, interaction.user.id)

    if channel is None and is_admin(interaction.user):
        ch = interaction.channel
        if isinstance(ch, discord.TextChannel) and ch.topic and ch.topic.startswith("vip:"):
            channel = ch

    if channel is None:
        await interaction.response.send_message("❌ You don't have a VIP room.", ephemeral=True)
        return

    owner_id = int(channel.topic.split(":")[1])
    await interaction.response.send_message("🗑️ Deleting your VIP room in 5 seconds...", ephemeral=True)
    await asyncio.sleep(5)
    await vip_delete_channel(channel, owner_id, f"Deleted by {interaction.user}")

@bot.tree.command(name="addviproom", description="Add a member to your private VIP room.")
@app_commands.describe(user="The member to add to your VIP room")
async def cmd_addviproom(interaction: discord.Interaction, user: discord.Member):
    if not interaction.guild:
        await interaction.response.send_message("❌ Server only.", ephemeral=True)
        return

    channel = await get_vip_channel(interaction.guild, interaction.user.id)
    if channel is None:
        await interaction.response.send_message(
            "❌ You don't have a private VIP room. Use `/createviproom` first.", ephemeral=True)
        return

    if user.id == interaction.user.id:
        await interaction.response.send_message(
            "❌ You're already in your own room.", ephemeral=True)
        return

    if user.bot:
        await interaction.response.send_message("❌ Can't add bots.", ephemeral=True)
        return

    existing_overwrite = channel.overwrites_for(user)
    if existing_overwrite.read_messages:
        await interaction.response.send_message(
            f"❌ **{user.display_name}** already has access to your VIP room.", ephemeral=True)
        return

    try:
        await channel.set_permissions(
            user,
            read_messages=True,
            send_messages=True,
            reason=f"Added by VIP room owner {interaction.user}"
        )
    except discord.Forbidden:
        await interaction.response.send_message("❌ Bot lacks permission to edit channel perms.", ephemeral=True)
        return

    await interaction.response.send_message(
        f"✅ **{user.display_name}** has been added to your VIP room {channel.mention}.", ephemeral=True)

    try:
        embed = discord.Embed(
            title="💎  VIP ACCESS GRANTED",
            description=f"👋 {user.mention} has been invited by {interaction.user.mention}.",
            color=C_VIP
        )
        _brand_embed(embed)
        await channel.send(embed=embed)
    except Exception as _err:
        print(f"[ERROR] Failed to send VIP add message: {_err}")

@bot.tree.command(name="removeviproom", description="Remove a member from your VIP room.")
@app_commands.describe(user="The member to remove from your VIP room")
async def cmd_removeviproom(interaction: discord.Interaction, user: discord.Member):
    if not interaction.guild:
        await interaction.response.send_message("❌ Server only.", ephemeral=True)
        return

    channel = await get_vip_channel(interaction.guild, interaction.user.id)
    if channel is None:
        await interaction.response.send_message(
            "❌ You don't have a VIP room.", ephemeral=True)
        return

    if user.id == interaction.user.id:
        await interaction.response.send_message(
            "❌ You can't remove yourself. Use `/deleteviproom` instead.", ephemeral=True)
        return

    try:
        await channel.set_permissions(user, overwrite=None)  # Remove all custom perms
    except discord.Forbidden:
        await interaction.response.send_message("❌ Bot lacks permission to edit channel.", ephemeral=True)
        return

    await interaction.response.send_message(
        f"✅ **{user.display_name}** has been removed from your VIP room.", ephemeral=True)

    try:
        await channel.send(embed=discord.Embed(
            description=f"🚫 {user.mention} has been removed from the VIP room.",
            color=C_LOSS
        ))
    except Exception as _err:
        print(f"[ERROR] Failed to send error message: {_err}")
        pass

class UpdateModal(discord.ui.Modal, title="✦ bloxysab — Update Log"):
    added = discord.ui.TextInput(
        label="🆕 New Features Added",
        placeholder="Added /colordice game\
Added VIP rooms\
New invite wager system",
        style=discord.TextStyle.paragraph,
        max_length=600,
        required=False
    )
    fixed = discord.ui.TextInput(
        label="🔧 Bug Fixes & Improvements",
        placeholder="Fixed withdrawal crash\
Improved mines multipliers",
        style=discord.TextStyle.paragraph,
        max_length=600,
        required=False
    )
    removed = discord.ui.TextInput(
        label="🗑️ Removed",
        placeholder="Removed /oldcommand",
        style=discord.TextStyle.paragraph,
        max_length=300,
        required=False
    )

    def __init__(self, channel: discord.TextChannel, version: str):
        super().__init__()
        self.channel = channel
        self.version = version

    def _format_section(self, raw: str, emoji: str) -> str:
        lines = []
        for line in raw.strip().splitlines():
            line = line.strip()
            if not line:
                continue
            for pfx in ("•", "-", "*", "–"):
                if line.startswith(pfx):
                    line = line[len(pfx):].strip()
            lines.append(f"{emoji} {line}")
        return "\
".join(lines)

    async def on_submit(self, interaction: discord.Interaction):
        sections = []
        if self.added.value.strip():
            lines = self._format_section(self.added.value, "🆕")
            sections.append(f"**New Features**\
{lines}")
        if self.fixed.value.strip():
            lines = self._format_section(self.fixed.value, "🔧")
            sections.append(f"**Fixes & Improvements**\
{lines}")
        if self.removed.value.strip():
            lines = self._format_section(self.removed.value, "🗑️")
            sections.append(f"**Removed**\
{lines}")

        if not sections:
            await interaction.response.send_message("❌ Fill in at least one section.", ephemeral=True)
            return

        description = "\
\
".join(sections)

        embed = discord.Embed(
            title=f"🎰 bloxysab Update — {self.version}",
            description=description,
            color=C_WIN
        )
        embed.set_author(name="bloxysab Update Log", icon_url=interaction.guild.icon.url if interaction.guild and interaction.guild.icon else None)
        embed.set_footer(text=f"Posted by {interaction.user.display_name} • {now_ts()}")

        await self.channel.send(embed=embed)
        await interaction.response.send_message(
            f"✅ Update log posted to {self.channel.mention}!", ephemeral=True)

        log_e = discord.Embed(title="📋 Update Log Posted", color=C_WIN)
        log_e.add_field(name="Posted by", value=interaction.user.mention, inline=True)
        log_e.add_field(name="Channel",   value=self.channel.mention,     inline=True)
        log_e.add_field(name="Version",   value=self.version,             inline=True)
        log_e.set_footer(text=now_ts())
        await send_log(log_e)

@bot.tree.command(name="update", description="[Admin] Post a casino update log to a channel.")
@app_commands.describe(
    channel="Channel to post the update in",
    version="Version label e.g. v1.2, Update #5 (optional)"
)
@admin_only()
async def cmd_update(
    interaction: discord.Interaction,
    channel: discord.TextChannel,
    version: str = ""
):
    v = f"v{version.strip()}" if version.strip() and not version.strip().lower().startswith("v") else (version.strip() or now_ts())
    await interaction.response.send_modal(UpdateModal(channel, v))

RAKEBACK_RATES = {
    "Bronze":       0.005,   # 0.5%
    "Silver":       0.010,   # 1.0%
    "Gold":         0.015,   # 1.5%
    "Platinum":     0.020,   # 2.0%
    "Ruby":         0.025,   # 2.5%
    "Emerald":      0.030,   # 3.0%
    "High Roller":  0.035,   # 3.5%
    "Whale":        0.045,   # 4.5%
    "Legend":       0.055,   # 5.5%
    "Diamond Whale":0.065,   # 6.5%  (leaderboard top 2-3)
    "Champion":     0.075,   # 7.5%  (leaderboard top 1)
}

def get_rakeback_rate(member: discord.Member) -> tuple[str, float]:
    """Return (rank_name, rate) based on member's current roles."""
    if any(r.name == CHAMPION_ROLE for r in member.roles):
        return "Champion", RAKEBACK_RATES["Champion"]
    if any(r.name == DIAMOND_WHALE_ROLE for r in member.roles):
        return "Diamond Whale", RAKEBACK_RATES["Diamond Whale"]
    return None, None  # resolved after DB lookup

@bot.tree.command(name="rakeback", description="Claim your daily rakeback based on your rank and wagered amount.")
async def cmd_rakeback(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    async with get_user_lock(interaction.user.id):
        conn = await get_conn()
        try:
            await ensure_user(conn, interaction.user)
            row = await get_user(conn, interaction.user.id)

            claim_row = await conn.fetchrow(
                "SELECT last_claim FROM daily_claims WHERE user_id=$1",
                f"rakeback_{interaction.user.id}"
            )
            now_dt  = datetime.now(timezone.utc)
            now_str = now_dt.strftime("%Y-%m-%d %H:%M:%S UTC")

            if claim_row and claim_row["last_claim"]:
                try:
                    raw     = claim_row["last_claim"].replace(" UTC", "")
                    last_dt = datetime.strptime(raw, "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)
                    diff    = now_dt - last_dt
                    if diff.total_seconds() < 86400:
                        remaining = timedelta(seconds=86400) - diff
                        hrs, rem  = divmod(int(remaining.total_seconds()), 3600)
                        mins      = rem // 60
                        await interaction.followup.send(
                            f"⏳ Already claimed today! Come back in **{hrs}h {mins}m**.",
                            ephemeral=True)
                        return
                except (ValueError, TypeError):
                    pass

            wagered_since = await conn.fetchval(
                "SELECT COALESCE(value, '0') FROM bot_settings WHERE key=$1",
                f"rakeback_wagered_{interaction.user.id}"
            )
            wagered_since = int(wagered_since) if wagered_since else 0

            if wagered_since <= 0:
                await interaction.followup.send(
                    "❌ You haven't wagered anything since your last claim. Play some games first!",
                    ephemeral=True)
                return

            rank_name_role, rate = get_rakeback_rate(interaction.user)
            if rank_name_role is None:
                wagered_total = row["wagered"] if row else 0
                _, rank_name_role, _, _, _ = get_rank(wagered_total)
            rate = RAKEBACK_RATES.get(rank_name_role, 0.005)

            reward = int(wagered_since * rate)
            if reward <= 0:
                await interaction.followup.send(
                    "❌ Rakeback amount is too small. Wager more first!", ephemeral=True)
                return

            await update_balance(conn, interaction.user.id, reward)
            await log_transaction(conn, interaction.user.id, "rakeback", reward,
                                  f"{rate*100:.1f}% of {wagered_since}")
            await add_wager_req(conn, interaction.user.id, reward, "rakeback")

            await conn.execute(
                """INSERT INTO bot_settings (key, value) VALUES ($1, '0')
                   ON CONFLICT (key) DO UPDATE SET value='0'""",
                f"rakeback_wagered_{interaction.user.id}"
            )

            await conn.execute(
                """INSERT INTO daily_claims (user_id, last_claim) VALUES ($1, $2)
                   ON CONFLICT (user_id) DO UPDATE SET last_claim=$2""",
                f"rakeback_{interaction.user.id}", now_str
            )

            new_bal = (await get_user(conn, interaction.user.id))["balance"]
        finally:
            await release_conn(conn)

    rate_table = ""
    for rname, rpct in RAKEBACK_RATES.items():
        marker = "◀ **You**" if rname == rank_name_role else ""
        rate_table += f"`{rpct*100:.1f}%` — {rname} {marker}\
"

    embed = discord.Embed(
        title="Rakeback Claimed",
        color=C_WIN
    )
    embed.add_field(name="Your Rank",        value=f"{rank_name_role}",                   inline=True)
    embed.add_field(name="Rakeback Rate",    value=f"{rate*100:.1f}%",                    inline=True)
    embed.add_field(name="Wagered (Period)", value=format_amount(wagered_since),           inline=True)
    embed.add_field(name="💎 You Received",  value=f"**{format_amount(reward)} 💎**",        inline=True)
    embed.add_field(name="New Balance",      value=format_amount(new_bal),                inline=True)
    embed.add_field(name="Next Claim",       value="In 24 hours",                         inline=True)
    embed.add_field(name="📊 All Rates", value=rate_table, inline=False)
    embed.set_footer(text=f"Rakeback resets every 24h • Wagered tracker reset to 0")
    await interaction.followup.send(embed=embed)

    log_e = discord.Embed(title="💸 Rakeback Claimed", color=C_WIN)
    log_e.add_field(name="User",    value=interaction.user.mention,  inline=True)
    log_e.add_field(name="Rank",    value=rank_name_role,            inline=True)
    log_e.add_field(name="Rate",    value=f"{rate*100:.1f}%",        inline=True)
    log_e.add_field(name="Wagered", value=format_amount(wagered_since), inline=True)
    log_e.add_field(name="Reward",  value=format_amount(reward),     inline=True)
    log_e.set_footer(text=now_ts())
    await send_log(log_e)

@bot.tree.command(name="sync", description="[Owner] Force sync all slash commands to this server instantly.")
@owner_only()
async def cmd_sync(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    try:
        bot.tree.copy_global_to(guild=interaction.guild)
        synced = await bot.tree.sync(guild=interaction.guild)
        await interaction.followup.send(
            f"✅ Synced **{len(synced)} commands** to **{interaction.guild.name}** instantly.\n"
            "All commands should now be available. Try Ctrl+R if not.",
            ephemeral=True
        )
        print(f"[SYNC] Manual sync: {len(synced)} commands → {interaction.guild.name}")
    except Exception as e:
        print(f"[ERROR] {type(e).__name__}: {e}")
        await interaction.followup.send(f"❌ Sync failed: {e}", ephemeral=True)

@bot.tree.command(name="clearsync", description="[Owner] Re-sync all slash commands.")
@owner_only()
async def cmd_clearsync(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    try:
        guild_obj = discord.Object(id=interaction.guild.id)
        bot.tree.copy_global_to(guild=guild_obj)
        guild_synced = await bot.tree.sync(guild=guild_obj)
        await interaction.followup.send(
            f"✅ Synced {len(guild_synced)} commands to this server!\nIf duplicates remain, press Ctrl+R in Discord to refresh.",
            ephemeral=True
        )
    except Exception as e:
        import traceback
        await interaction.followup.send(f"❌ Error: {e}\n```{traceback.format_exc()[-500:]}```", ephemeral=True)

import hashlib

QUEST_MIN_BET  = 100_000   # 100K gems minimum bet for quest to count
QUEST_DAY_CAP  = 9_000_000  # 9M gems max earnable from quests per day (3 quests × 3M max)

QUEST_POOL = [
    {"id": "play_coinflip_3",  "desc": "Play 3 Coinflip games",       "type": "play",   "game": "coinflip",  "target": 3,  "reward": 1_000_000},
    {"id": "play_coinflip_5",  "desc": "Play 5 Coinflip games",       "type": "play",   "game": "coinflip",  "target": 5,  "reward": 1_500_000},
    {"id": "play_mines_3",     "desc": "Play 3 Mines games",          "type": "play",   "game": "mines",     "target": 3,  "reward": 1_200_000},
    {"id": "play_mines_5",     "desc": "Play 5 Mines games",          "type": "play",   "game": "mines",     "target": 5,  "reward": 1_800_000},
    {"id": "play_blackjack_3", "desc": "Play 3 Blackjack games",      "type": "play",   "game": "blackjack", "target": 3,  "reward": 1_000_000},
    {"id": "play_blackjack_5", "desc": "Play 5 Blackjack games",      "type": "play",   "game": "blackjack", "target": 5,  "reward": 1_500_000},
    {"id": "play_roulette_3",  "desc": "Play 3 Roulette games",       "type": "play",   "game": "roulette",  "target": 3,  "reward": 1_000_000},
    {"id": "play_dice_3",      "desc": "Play 3 Dice games",           "type": "play",   "game": "dice",      "target": 3,  "reward": 1_000_000},
    {"id": "play_dice_5",      "desc": "Play 5 Dice games",           "type": "play",   "game": "dice",      "target": 5,  "reward": 1_500_000},
    {"id": "play_hilo_5",      "desc": "Play 5 HiLo games",           "type": "play",   "game": "hilo",      "target": 5,  "reward": 1_200_000},
    {"id": "play_any_5",       "desc": "Play 5 games (any)",          "type": "play",   "game": "any",       "target": 5,  "reward": 1_000_000},
    {"id": "play_any_10",      "desc": "Play 10 games (any)",         "type": "play",   "game": "any",       "target": 10, "reward": 1_800_000},
    {"id": "play_upgrader_3",  "desc": "Play 3 Upgrader games",       "type": "play",   "game": "upgrader",  "target": 3,  "reward": 1_200_000},
    {"id": "play_baccarat_3",  "desc": "Play 3 Baccarat games",       "type": "play",   "game": "baccarat",  "target": 3,  "reward": 1_000_000},
    {"id": "play_horserace_2", "desc": "Play 2 Horse Race games",     "type": "play",   "game": "horserace", "target": 2,  "reward": 1_000_000},
    {"id": "play_slots_5",     "desc": "Play 5 Slots games",          "type": "play",   "game": "slots",     "target": 5,  "reward": 1_200_000},
    {"id": "play_towers_3",    "desc": "Play 3 Towers games",         "type": "play",   "game": "towers",    "target": 3,  "reward": 1_100_000},
    {"id": "play_balloon_3",   "desc": "Play 3 Balloon games",        "type": "play",   "game": "balloon",   "target": 3,  "reward": 1_000_000},
    {"id": "wager_100k",       "desc": "Wager 100K gems total",        "type": "wager",  "game": "any",       "target": 100_000,   "reward": 1_000_000},
    {"id": "wager_500k",       "desc": "Wager 500K gems total",        "type": "wager",  "game": "any",       "target": 500_000,   "reward": 1_500_000},
    {"id": "wager_1m",         "desc": "Wager 1M gems total",          "type": "wager",  "game": "any",       "target": 1_000_000, "reward": 2_000_000},
    {"id": "wager_5m",         "desc": "Wager 5M gems total",          "type": "wager",  "game": "any",       "target": 5_000_000, "reward": 3_000_000},
    {"id": "win_coinflip_2",   "desc": "Win 2 Coinflip games",        "type": "win",    "game": "coinflip",  "target": 2,  "reward": 1_000_000},
    {"id": "win_any_3",        "desc": "Win 3 games (any)",           "type": "win",    "game": "any",       "target": 3,  "reward": 1_000_000},
    {"id": "win_any_5",        "desc": "Win 5 games (any)",           "type": "win",    "game": "any",       "target": 5,  "reward": 1_500_000},
    {"id": "win_any_10",       "desc": "Win 10 games (any)",          "type": "win",    "game": "any",       "target": 10, "reward": 2_500_000},
    {"id": "win_streak_3",     "desc": "Win 3 games in a row",        "type": "streak", "game": "any",       "target": 3,  "reward": 1_500_000},
    {"id": "win_streak_5",     "desc": "Win 5 games in a row",        "type": "streak", "game": "any",       "target": 5,  "reward": 3_000_000},
    {"id": "tip_someone",      "desc": "Tip another user any amount", "type": "tip",    "game": "any",       "target": 1,  "reward": 1_000_000},
    {"id": "daily_claim",      "desc": "Claim your /daily bonus",     "type": "daily",  "game": "any",       "target": 1,  "reward": 1_000_000},
]

QUEST_EMOJIS = {"play": "🎮", "wager": "💰", "win": "🏆", "streak": "🔥", "tip": "💸", "daily": "📅"}

def get_daily_quests(user_id: int, date_str: str, count: int = 3) -> list:
    """Pick 3 deterministic daily quests whose combined reward stays ≤ QUEST_DAY_CAP."""
    seed_str = f"{user_id}:{date_str}"
    seed = int(hashlib.md5(seed_str.encode()).hexdigest(), 16)
    rng = random.Random(seed)

    pool = QUEST_POOL.copy()
    rng.shuffle(pool)

    chosen = []
    total_reward = 0
    for q in pool:
        if len(chosen) >= count:
            break
        if total_reward + q["reward"] <= QUEST_DAY_CAP:
            chosen.append({**q})
            total_reward += q["reward"]

    if not chosen:
        fallback = sorted(QUEST_POOL, key=lambda x: x["reward"])[:count]
        chosen = [{**q} for q in fallback]

    return chosen

async def ensure_quest_tables(conn):
    await conn.execute("""
        CREATE TABLE IF NOT EXISTS quest_progress (
            user_id  TEXT NOT NULL,
            date_str TEXT NOT NULL,
            quest_id TEXT NOT NULL,
            progress BIGINT NOT NULL DEFAULT 0,
            claimed  BOOLEAN NOT NULL DEFAULT FALSE,
            PRIMARY KEY (user_id, date_str, quest_id)
        )
    """)

async def get_quest_progress(conn, user_id: int, date_str: str, quest_id: str) -> dict:
    row = await conn.fetchrow(
        "SELECT progress, claimed FROM quest_progress WHERE user_id=$1 AND date_str=$2 AND quest_id=$3",
        str(user_id), date_str, quest_id
    )
    return {"progress": row["progress"] if row else 0, "claimed": row["claimed"] if row else False}

async def reset_streak_quest(conn, user_id: int):
    """Reset streak quest progress to 0 when a game is lost."""
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    quests = get_daily_quests(user_id, today)
    for q in quests:
        if q["type"] == "streak":
            await conn.execute(
                """UPDATE quest_progress SET progress = 0
                   WHERE user_id=$1 AND date_str=$2 AND quest_id=$3 AND claimed=FALSE""",
                str(user_id), today, q["id"]
            )

async def update_quest_progress(conn, user_id: int, quest_type: str, game: str, amount: int = 1, bet: int = 0):
    """Update quest progress. Auto-pays reward the moment a quest completes — no /quests needed.
    tip and daily quests have no minimum bet requirement."""
    try:
        await ensure_quest_tables(conn)
    except Exception:
        pass
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    quests = get_daily_quests(user_id, today)
    for q in quests:
        if q["type"] != quest_type:
            continue
        if q["game"] != "any" and q["game"] != game:
            continue
        if q["type"] not in ("tip", "daily") and bet < QUEST_MIN_BET:
            continue

        prev = await conn.fetchrow(
            "SELECT progress, claimed FROM quest_progress WHERE user_id=$1 AND date_str=$2 AND quest_id=$3",
            str(user_id), today, q["id"]
        )
        prev_progress = prev["progress"] if prev else 0
        prev_claimed  = prev["claimed"]  if prev else False

        await conn.execute("""
            INSERT INTO quest_progress (user_id, date_str, quest_id, progress, claimed)
            VALUES ($1, $2, $3, $4, FALSE)
            ON CONFLICT (user_id, date_str, quest_id)
            DO UPDATE SET progress = LEAST(quest_progress.progress + $4, $5)
        """, str(user_id), today, q["id"], amount, q["target"])

        new_progress = min(prev_progress + amount, q["target"])
        just_completed = new_progress >= q["target"] and prev_progress < q["target"] and not prev_claimed

        if just_completed:
            reward = q["reward"]
            await update_balance(conn, user_id, reward)
            await log_transaction(conn, user_id, "quest_reward", reward, q["desc"])
            await conn.execute("""
                INSERT INTO quest_progress (user_id, date_str, quest_id, progress, claimed)
                VALUES ($1, $2, $3, $4, TRUE)
                ON CONFLICT (user_id, date_str, quest_id)
                DO UPDATE SET claimed = TRUE
            """, str(user_id), today, q["id"], new_progress)

            try:
                user = bot.get_user(user_id)
                if user is None:
                    user = await bot.fetch_user(user_id)
                if user:
                    embed = discord.Embed(
                        title="Quest Complete!",
                        description=f"**{q['desc']}**\n\n**+{format_amount(reward)}** 💎 has been added to your balance automatically.",
                        color=C_VIP
                    )
                    _brand_embed(embed)
                    await user.send(embed=embed)
            except Exception as _dm_err:
                print(f"[QUEST] Could not DM {user_id}: {_dm_err}")

@bot.tree.command(name="quests", description="View and claim your daily quests. Refreshes every 24 hours.")
async def cmd_quests(interaction: discord.Interaction):
    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        await ensure_quest_tables(conn)

        today   = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        quests  = get_daily_quests(interaction.user.id, today)
        lines   = []

        for q in quests:
            prog     = await get_quest_progress(conn, interaction.user.id, today, q["id"])
            progress = prog["progress"]
            claimed  = prog["claimed"]
            target   = q["target"]
            reward   = q["reward"]
            emoji    = QUEST_EMOJIS.get(q["type"], "🎯")
            done     = progress >= target

            if done and not claimed:
                await conn.execute("""
                    INSERT INTO quest_progress (user_id, date_str, quest_id, progress, claimed)
                    VALUES ($1, $2, $3, $4, TRUE)
                    ON CONFLICT (user_id, date_str, quest_id)
                    DO UPDATE SET claimed = TRUE
                """, str(interaction.user.id), today, q["id"], progress)
                claimed = True

            bar_filled = min(10, int((progress / target) * 10))
            bar        = "\u2588" * bar_filled + "\u2591" * (10 - bar_filled)

            if claimed:
                status = "\u2705 **CLAIMED**"
            elif done:
                status = "\U0001f381 **READY**"
            else:
                status = f"`{bar}` {progress}/{target}"

            lines.append(
                f"{emoji}  **{q['desc']}**\n"
                f"└ Reward: **+{format_amount(reward)}**  ·  {status}"
            )

        now_utc  = datetime.now(timezone.utc)
        tomorrow = (now_utc + timedelta(days=1)).replace(hour=0, minute=0, second=0, microsecond=0)
        remaining = tomorrow - now_utc
        hrs, rem = divmod(int(remaining.total_seconds()), 3600)
        mins     = rem // 60

        total_reward   = sum(q["reward"] for q in quests)
        claimed_reward = sum(
            q["reward"] for q in quests
            if (await get_quest_progress(conn, interaction.user.id, today, q["id"]))["claimed"]
        )

        embed = discord.Embed(
            title="🎯  Daily Quests",
            description="\n\n".join(lines),
            color=C_VIP
        )
        embed.add_field(
            name="Today's Pot",
            value=f"`{format_amount(total_reward)} gems`",
            inline=True
        )
        embed.add_field(
            name="Earned Today",
            value=f"`{format_amount(claimed_reward)} gems`",
            inline=True
        )
        embed.add_field(
            name="Daily Cap",
            value=f"`{format_amount(QUEST_DAY_CAP)} gems`",
            inline=True
        )
        embed.set_thumbnail(url=await get_avatar(interaction.user))
        _brand_embed(embed)

        await interaction.response.send_message(embed=embed, ephemeral=True)
    except Exception as e:
        print(f"[ERROR] quests: {type(e).__name__}: {e}")
        import traceback; traceback.print_exc()
        if interaction.response.is_done():
            await interaction.followup.send("\u274c Something went wrong.", ephemeral=True)
        else:
            await interaction.response.send_message("\u274c Something went wrong.", ephemeral=True)
    finally:
        await release_conn(conn)

AFFILIATE_RATE = 0.005  # 0.5%

async def ensure_affiliate_tables(conn):
    await conn.execute("""
        CREATE TABLE IF NOT EXISTS affiliate_codes (
            user_id         TEXT PRIMARY KEY,
            code            TEXT UNIQUE NOT NULL,
            pending_balance BIGINT NOT NULL DEFAULT 0,
            total_earned    BIGINT NOT NULL DEFAULT 0,
            referral_count  INT NOT NULL DEFAULT 0,
            created_at      TEXT NOT NULL
        )
    """)
    await conn.execute("""
        ALTER TABLE affiliate_codes ADD COLUMN IF NOT EXISTS pending_balance BIGINT NOT NULL DEFAULT 0
    """)
    await conn.execute("""
        CREATE TABLE IF NOT EXISTS affiliate_uses (
            referral_id   TEXT PRIMARY KEY,
            referrer_id   TEXT NOT NULL,
            code          TEXT NOT NULL,
            total_wagered BIGINT NOT NULL DEFAULT 0,
            total_earned  BIGINT NOT NULL DEFAULT 0,
            used_at       TEXT NOT NULL
        )
    """)

def generate_affiliate_code(user: discord.User) -> str:
    base   = user.name.upper().replace(" ", "")[:6]
    suffix = str(user.id)[-4:]
    return f"{base}{suffix}"

@bot.tree.command(name="affiliatecode", description="Get your unique affiliate code. Share it to earn 0.5% of referral wagers.")
async def cmd_affiliatecode(interaction: discord.Interaction):
    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        await ensure_affiliate_tables(conn)

        uid = str(interaction.user.id)
        row = await conn.fetchrow("SELECT * FROM affiliate_codes WHERE user_id=$1", uid)

        if not row:
            code = generate_affiliate_code(interaction.user)
            existing = await conn.fetchrow("SELECT user_id FROM affiliate_codes WHERE code=$1", code)
            if existing:
                code = code + str(random.randint(10, 99))
            await conn.execute(
                "INSERT INTO affiliate_codes (user_id, code, pending_balance, total_earned, referral_count, created_at) VALUES ($1, $2, 0, 0, 0, $3) ON CONFLICT (user_id) DO NOTHING",
                uid, code, datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
            )
            row = await conn.fetchrow("SELECT * FROM affiliate_codes WHERE user_id=$1", uid)

        embed = discord.Embed(title="Your Affiliate Code", color=C_VIP)
        embed.add_field(name="Your Code",          value=f"```{row['code']}```",                            inline=False)
        embed.add_field(name="\u23f3 Pending",      value=f"\U0001f48e {format_amount(row['pending_balance'])}", inline=True)
        embed.add_field(name="\U0001f48e Total Earned", value=f"\U0001f48e {format_amount(row['total_earned'])}",    inline=True)
        embed.add_field(name="\U0001f465 Referrals",    value=str(row["referral_count"]),                       inline=True)
        embed.add_field(name="\U0001f4c8 Rate",     value="0.5% of all their wagers forever",              inline=True)
        embed.add_field(
            name="How it works",
            value=(
                "Share your code. When someone uses `/affiliate <code>` they link to you.\n"
                "You earn **0.5%** of every coin they wager, forever.\n"
                "Earnings build up in **Pending** — use `/affiliateclaim` to withdraw."
            ),
            inline=False
        )
        embed.set_thumbnail(url=await get_avatar(interaction.user))
        await interaction.response.send_message(embed=embed, ephemeral=True)
    except Exception as e:
        print(f"[ERROR] affiliatecode: {type(e).__name__}: {e}")
        import traceback; traceback.print_exc()
        if interaction.response.is_done():
            await interaction.followup.send("\u274c Something went wrong.", ephemeral=True)
        else:
            await interaction.response.send_message("\u274c Something went wrong.", ephemeral=True)
    finally:
        await release_conn(conn)

@bot.tree.command(name="affiliate", description="Enter an affiliate code to link your account to a referrer.")
@app_commands.describe(code="The affiliate code you received")
async def cmd_affiliate(interaction: discord.Interaction, code: str):
    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        await ensure_affiliate_tables(conn)

        uid  = str(interaction.user.id)
        code = code.upper().strip()

        existing = await conn.fetchrow("SELECT referrer_id FROM affiliate_uses WHERE referral_id=$1", uid)
        if existing:
            await interaction.response.send_message("\u274c You have already used an affiliate code. You can only link once.", ephemeral=True)
            return

        code_row = await conn.fetchrow("SELECT * FROM affiliate_codes WHERE code=$1", code)
        if not code_row:
            await interaction.response.send_message("\u274c Invalid affiliate code.", ephemeral=True)
            return

        if code_row["user_id"] == uid:
            await interaction.response.send_message("\u274c You can't use your own affiliate code.", ephemeral=True)
            return

        await conn.execute(
            "INSERT INTO affiliate_uses (referral_id, referrer_id, code, total_wagered, total_earned, used_at) VALUES ($1, $2, $3, 0, 0, $4)",
            uid, code_row["user_id"], code, datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
        )
        await conn.execute("UPDATE affiliate_codes SET referral_count = referral_count + 1 WHERE code=$1", code)

        try:
            referrer     = await bot.fetch_user(int(code_row["user_id"]))
            referrer_name = referrer.name if referrer else "Unknown"
        except Exception:
            referrer_name = "Unknown"

        embed = discord.Embed(
            title="Affiliate Code Applied",
            description=f"You are now linked to **{referrer_name}**.\nThey will earn **0.5%** of your wagers forever.",
            color=C_WIN
        )
        embed.set_footer(text="This link is permanent. Good luck!")
        await interaction.response.send_message(embed=embed, ephemeral=True)
    except Exception as e:
        print(f"[ERROR] affiliate: {type(e).__name__}: {e}")
        import traceback; traceback.print_exc()
        if interaction.response.is_done():
            await interaction.followup.send("\u274c Something went wrong.", ephemeral=True)
        else:
            await interaction.response.send_message("\u274c Something went wrong.", ephemeral=True)
    finally:
        await release_conn(conn)

@bot.tree.command(name="affiliateclaim", description="Claim your accumulated affiliate earnings.")
async def cmd_affiliateclaim(interaction: discord.Interaction):
    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        await ensure_affiliate_tables(conn)

        uid = str(interaction.user.id)
        row = await conn.fetchrow("SELECT * FROM affiliate_codes WHERE user_id=$1", uid)

        if not row:
            await interaction.response.send_message(
                "\u274c You don't have an affiliate code yet. Use `/affiliatecode` first.", ephemeral=True
            )
            return

        pending = row["pending_balance"]
        if pending <= 0:
            await interaction.response.send_message(
                "\u274c No pending earnings to claim yet. Share your code and wait for referrals to play!",
                ephemeral=True
            )
            return

        await update_balance(conn, interaction.user.id, pending)
        await log_transaction(conn, interaction.user.id, "affiliate_claim", pending, "Affiliate earnings claimed")
        await add_wager_req(conn, interaction.user.id, pending, "affiliate_claim")
        await conn.execute("UPDATE affiliate_codes SET pending_balance = 0 WHERE user_id=$1", uid)

        embed = discord.Embed(
            title="Earnings Claimed",
            description=f"You received **\U0001f48e {format_amount(pending)}** from your affiliate earnings.",
            color=C_WIN
        )
        embed.add_field(name="All-Time Earned", value=f"\U0001f48e {format_amount(row['total_earned'])}", inline=True)
        embed.add_field(name="Referrals",        value=str(row["referral_count"]),                       inline=True)
        embed.set_footer(text="Keep sharing your code to earn more!")
        embed.set_thumbnail(url=await get_avatar(interaction.user))
        await interaction.response.send_message(embed=embed)
    except Exception as e:
        print(f"[ERROR] affiliateclaim: {type(e).__name__}: {e}")
        import traceback; traceback.print_exc()
        if interaction.response.is_done():
            await interaction.followup.send("\u274c Something went wrong.", ephemeral=True)
        else:
            await interaction.response.send_message("\u274c Something went wrong.", ephemeral=True)
    finally:
        await release_conn(conn)

async def pay_affiliate(conn, referral_id: int, bet: int):
    """Accumulate 0.5% of bet into referrer pending_balance. User claims manually via /affiliateclaim."""
    try:
        row = await conn.fetchrow("SELECT referrer_id FROM affiliate_uses WHERE referral_id=$1", str(referral_id))
        if not row:
            return
        referrer_id = int(row["referrer_id"])
        commission  = max(1, int(bet * AFFILIATE_RATE))
        await conn.execute("""
            UPDATE affiliate_codes
            SET pending_balance = pending_balance + $1,
                total_earned    = total_earned    + $1
            WHERE user_id = $2
        """, commission, str(referrer_id))
        await conn.execute("""
            UPDATE affiliate_uses
            SET total_wagered = total_wagered + $1,
                total_earned  = total_earned  + $2
            WHERE referral_id = $3
        """, bet, commission, str(referral_id))
    except Exception as e:
        print(f"[AFFILIATE] Error: {type(e).__name__}: {e}")

MESSAGE_REWARD_AMOUNT    = 25_000_000  # 25M gems per 500 messages
MESSAGE_REWARD_EVERY     = 500
MESSAGE_COOLDOWN_SECS    = 10
MESSAGE_MIN_LENGTH       = 5
MESSAGE_MIN_UNIQUE_WORDS = 3

_msg_cooldowns: dict = {}    # user_id -> last counted timestamp
_msg_last_text: dict = {}    # user_id -> last counted message
_msg_spam_strikes: dict = {} # user_id -> strike count
_msg_dm_cooldown: dict = {}  # user_id -> last DM warning timestamp

SPAM_STRIKE_THRESHOLD = 3       # warn after this many spam attempts in a row
SPAM_DM_COOLDOWN_SECS = 900     # only send DM warning once per 15 minutes per user

SPAM_REASONS = {
    "cooldown":    "sending messages too fast (10 second cooldown between counted messages)",
    "repeat":      "sending the same message twice in a row",
    "low_unique":  "sending a message with fewer than 3 unique words",
    "spam_chars":  "sending repeated characters (e.g. `aaaaaaa`)",
    "spam_repeat": "repeating the same word over and over",
    "too_short":   "sending messages shorter than 5 characters",
    "command":     None,  # don't warn for commands
}

async def ensure_message_tables(conn):
    await conn.execute("""
        CREATE TABLE IF NOT EXISTS message_counts (
            user_id         TEXT PRIMARY KEY,
            total_count     BIGINT NOT NULL DEFAULT 0,
            unclaimed_miles INT    NOT NULL DEFAULT 0,
            total_claimed   INT    NOT NULL DEFAULT 0
        )
    """)

def message_check(content: str, user_id: int) -> tuple:
    """Returns (is_valid: bool, reason: str)"""
    import time
    content = content.strip()

    if not content or len(content) < MESSAGE_MIN_LENGTH:
        return False, "too_short"
    if content.startswith("/") or content.startswith("!"):
        return False, "command"

    now = time.time()
    if now - _msg_cooldowns.get(user_id, 0) < MESSAGE_COOLDOWN_SECS:
        return False, "cooldown"

    normalized = " ".join(content.lower().split())

    if normalized == _msg_last_text.get(user_id, ""):
        return False, "repeat"

    words  = normalized.split()
    unique = set(words)

    if len(unique) < MESSAGE_MIN_UNIQUE_WORDS:
        return False, "low_unique"

    for w in words:
        if len(w) >= 4 and len(set(w)) == 1:
            return False, "spam_chars"

    if len(words) >= 3 and len(unique) == 1:
        return False, "spam_repeat"

    return True, "ok"

async def maybe_warn_spammer(user: discord.Member, reason: str):
    """Track spam strikes and DM user a warning after repeated spam."""
    import time

    if SPAM_REASONS.get(reason) is None:
        return  # Don't warn for commands/short messages

    uid = user.id
    _msg_spam_strikes[uid] = _msg_spam_strikes.get(uid, 0) + 1

    if _msg_spam_strikes[uid] < SPAM_STRIKE_THRESHOLD:
        return  # Not enough strikes yet

    now = time.time()
    if now - _msg_dm_cooldown.get(uid, 0) < SPAM_DM_COOLDOWN_SECS:
        return

    _msg_dm_cooldown[uid] = now
    _msg_spam_strikes[uid] = 0  # Reset strikes after warning

    readable_reason = SPAM_REASONS.get(reason, reason)
    try:
        embed = discord.Embed(
            title="⚠️  Message Rewards Warning",
            description=(
                f"Hey {user.mention}! Your recent messages are **not counting** toward your message rewards "
                f"because you are **{readable_reason}**.\n\n"
                "**To earn message rewards your messages must:**\n"
                "• Be at least **5 characters** long\n"
                "• Have at least **3 unique words**\n"
                "• Not repeat your last message\n"
                "• Not be sent faster than every **10 seconds**\n"
                "• Not contain spammy repeated characters\n\n"
                "Keep chatting naturally and you will earn **💎 25M gems every 500 messages**!\n"
                "_(This warning won't be sent again for 15 minutes)_"
            ),
            color=C_WARN
        )
        _brand_embed(embed)
        await user.send(embed=embed)
        print(f"[MSG_REWARD] Warned {user.name} for spam ({reason})")
    except Exception as e:
        print(f"[MSG_REWARD] DM warning failed: {e}")

@bot.event
async def on_message(message: discord.Message):
    if not message.guild or message.author.bot or message.webhook_id:
        return
    if message.guild.id != GUILD_ID:
        return

    user = message.author
    valid, reason = message_check(message.content, user.id)

    if not valid:
        await maybe_warn_spammer(user, reason)
        return

    import time as _mt
    _msg_cooldowns[user.id]    = _mt.time()
    _msg_last_text[user.id]    = " ".join(message.content.lower().split())
    _msg_spam_strikes[user.id] = 0

    conn = await get_conn()
    try:
        await ensure_message_tables(conn)
        row = await conn.fetchrow(
            "SELECT total_count FROM message_counts WHERE user_id=$1",
            str(user.id)
        )
        old_total = row["total_count"] if row else 0
        new_total = old_total + 1
        hit_milestone = (new_total % MESSAGE_REWARD_EVERY == 0)

        await conn.execute("""
            INSERT INTO message_counts (user_id, total_count, unclaimed_miles, total_claimed)
            VALUES ($1, 1, 0, 0)
            ON CONFLICT (user_id) DO UPDATE SET
                total_count     = message_counts.total_count + 1,
                unclaimed_miles = message_counts.unclaimed_miles
                                  + CASE WHEN (message_counts.total_count + 1) % $2 = 0 THEN 1 ELSE 0 END
        """, str(user.id), MESSAGE_REWARD_EVERY)

        if hit_milestone:
            try:
                note = discord.Embed(
                    title="🎉  Message Milestone!",
                    description=(
                        f"🏆 You've sent **{new_total}** messages!\n\n"
                        f"💎 Use `/redeemmessagerewards` to claim **{format_amount(MESSAGE_REWARD_AMOUNT)} gems**!"
                    ),
                    color=C_VIP
                )
                _brand_embed(note)
                await user.send(embed=note)
            except Exception:
                pass
    except Exception as e:
        print(f"[MSG_REWARD] on_message error for {user}: {e}")
    finally:
        await release_conn(conn)

import time as _time

_raid_ban_log:  dict = {}
_raid_kick_log: dict = {}
_raid_join_log: list = []

RAID_BAN_THRESHOLD   = 5
RAID_KICK_THRESHOLD  = 10
RAID_JOIN_THRESHOLD  = 15
RAID_WINDOW          = 10
RAID_JOIN_WINDOW     = 8
RAID_TIMEOUT_MINUTES = 60

async def _raid_punish(guild: discord.Guild, member: discord.Member, reason: str):
    log_e = discord.Embed(title="Anti-Raid Action", color=0xFF0000)
    log_e.add_field(name="Target",  value=f"{member} ({member.id})", inline=True)
    log_e.add_field(name="Reason",  value=reason,                    inline=True)
    log_e.set_footer(text=now_ts())
    try:
        await guild.ban(member, reason=f"[Anti-Raid] {reason}", delete_message_days=0)
        log_e.add_field(name="Action", value="🔨 Banned", inline=True)
    except discord.Forbidden:
        try:
            import datetime as _dt
            until = discord.utils.utcnow() + _dt.timedelta(minutes=RAID_TIMEOUT_MINUTES)
            await member.timeout(until, reason=f"[Anti-Raid] {reason}")
            log_e.add_field(name="Action", value=f"⏱️ Timed out {RAID_TIMEOUT_MINUTES}m", inline=True)
        except Exception as e:
            log_e.add_field(name="Action", value=f"❌ Failed: {e}", inline=True)
    except Exception as e:
        log_e.add_field(name="Action", value=f"❌ Failed: {e}", inline=True)
    await send_finance_log(log_e)
    print(f"[ANTI-RAID] {reason} → {member}")

async def on_member_join_raid_check(member: discord.Member):
    now = _time.time()
    _raid_join_log.append(now)
    recent = [t for t in _raid_join_log if now - t < RAID_JOIN_WINDOW]
    _raid_join_log.clear()
    _raid_join_log.extend(recent)
    if len(_raid_join_log) >= RAID_JOIN_THRESHOLD:
        _raid_join_log.clear()
        log_e = discord.Embed(
            title="🚨 Join Raid Detected",
            description=f"**{RAID_JOIN_THRESHOLD}+ joins in {RAID_JOIN_WINDOW}s**",
            color=0xFF0000
        )
        log_e.set_footer(text=now_ts())
        await send_finance_log(log_e)
        print(f"[ANTI-RAID] Join flood detected")

@bot.event
async def on_audit_log_entry_create(entry: discord.AuditLogEntry):
    guild = entry.guild
    actor = entry.user
    if not actor or actor.bot:
        return
    now = _time.time()
    if entry.action == discord.AuditLogAction.ban:
        log = _raid_ban_log.setdefault(actor.id, [])
        log.append(now)
        _raid_ban_log[actor.id] = [t for t in log if now - t < RAID_WINDOW]
        if len(_raid_ban_log[actor.id]) >= RAID_BAN_THRESHOLD:
            _raid_ban_log[actor.id] = []
            member = guild.get_member(actor.id)
            if member and not is_admin(member):
                await _raid_punish(guild, member, f"Mass ban — {RAID_BAN_THRESHOLD}+ bans in {RAID_WINDOW}s")
    elif entry.action == discord.AuditLogAction.kick:
        log = _raid_kick_log.setdefault(actor.id, [])
        log.append(now)
        _raid_kick_log[actor.id] = [t for t in log if now - t < RAID_WINDOW]
        if len(_raid_kick_log[actor.id]) >= RAID_KICK_THRESHOLD:
            _raid_kick_log[actor.id] = []
            member = guild.get_member(actor.id)
            if member and not is_admin(member):
                await _raid_punish(guild, member, f"Mass kick — {RAID_KICK_THRESHOLD}+ kicks in {RAID_WINDOW}s")

async def _ensure_member_snapshot_table(conn):
    await conn.execute("""
        CREATE TABLE IF NOT EXISTS member_snapshot (
            user_id     TEXT PRIMARY KEY,
            username    TEXT,
            first_seen  TEXT,
            last_seen   TEXT
        )
    """)
    await conn.execute("""
        CREATE TABLE IF NOT EXISTS daily_dm_config (
            id          SERIAL PRIMARY KEY,
            send_hour   INT  DEFAULT 12,
            send_minute INT  DEFAULT 0,
            message     TEXT DEFAULT '',
            title       TEXT DEFAULT 'bloxysab Update',
            color       TEXT DEFAULT 'gold',
            enabled     BOOL DEFAULT FALSE,
            last_sent   TEXT DEFAULT ''
        )
    """)
    await conn.execute("""
        INSERT INTO daily_dm_config (id) VALUES (1) ON CONFLICT DO NOTHING
    """)

async def _snapshot_member(conn, user):
    """Upsert a member into the snapshot table."""
    now = now_ts()
    await conn.execute("""
        INSERT INTO member_snapshot (user_id, username, first_seen, last_seen)
        VALUES ($1, $2, $3, $3)
        ON CONFLICT (user_id) DO UPDATE
        SET username=$2, last_seen=$3
    """, str(user.id), getattr(user, 'name', str(user.id)), now)

async def _snapshot_all_members():
    """On startup, snapshot every current guild member."""
    await asyncio.sleep(5)
    guild = bot.get_guild(GUILD_ID)
    if not guild:
        return
    conn = await get_conn()
    try:
        await _ensure_member_snapshot_table(conn)
        count = 0
        for member in guild.members:
            if member.bot:
                continue
            await _snapshot_member(conn, member)
            count += 1
        print(f"[SNAPSHOT] Saved {count} members to snapshot table")
    except Exception as e:
        print(f"[SNAPSHOT] Error: {e}")
    finally:
        await release_conn(conn)

async def _send_daily_dms(title: str, message: str, color_name: str):
    """Blast daily DM to every saved member."""
    color_map = {"green": 0x2ECC71, "red": 0xE74C3C, "blue": 0x3498DB, "gold": 0xE8B84B, "purple": 0x9B59B6}
    color = color_map.get(color_name.lower(), 0xE8B84B)

    conn = await get_conn()
    try:
        rows = await conn.fetch("SELECT user_id, username FROM member_snapshot")
    finally:
        await release_conn(conn)

    sent = failed = skipped = 0
    for row in rows:
        try:
            user = await bot.fetch_user(int(row["user_id"]))
            embed = discord.Embed(
                title=f"📣 {title}",
                description=f"{user.mention}\n\n{message}",
                color=color
            )
            embed.set_footer(text=f"bloxysab  ·  {now_ts()}")
            await user.send(embed=embed)
            sent += 1
        except discord.Forbidden:
            skipped += 1
        except discord.HTTPException as e:
            if e.status == 429:
                await asyncio.sleep(float(e.retry_after) + 0.5)
                try:
                    if 'user' in dir() and 'embed' in dir():
                        await user.send(embed=embed)
                        sent += 1
                    else:
                        failed += 1
                except Exception:
                    failed += 1
            else:
                failed += 1
        except Exception:
            failed += 1
        await asyncio.sleep(1.2)

    log_e = discord.Embed(title="📣 Daily DM Sent", color=0xE8B84B)
    log_e.add_field(name="✅ Sent",    value=str(sent),    inline=True)
    log_e.add_field(name="🔕 Skipped", value=str(skipped), inline=True)
    log_e.add_field(name="❌ Failed",  value=str(failed),  inline=True)
    log_e.add_field(name="📌 Title",   value=title,        inline=False)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)
    print(f"[DAILY DM] Done — sent:{sent} skipped:{skipped} failed:{failed}")

async def _daily_dm_loop():
    """Background loop — fires the daily DM at the configured time."""
    await asyncio.sleep(10)
    while True:
        try:
            conn = await get_conn()
            try:
                await _ensure_member_snapshot_table(conn)
                cfg = await conn.fetchrow("SELECT * FROM daily_dm_config WHERE id=1")
            finally:
                await release_conn(conn)

            if cfg and cfg["enabled"] and cfg["message"]:
                from datetime import datetime, timezone
                now = datetime.now(timezone.utc)
                target_hour   = cfg["send_hour"]
                target_minute = cfg["send_minute"]
                last_sent     = cfg["last_sent"] or ""
                today_key     = now.strftime("%Y-%m-%d")

                if (now.hour == target_hour and now.minute == target_minute
                        and today_key not in last_sent):
                    conn = await get_conn()
                    try:
                        await conn.execute(
                            "UPDATE daily_dm_config SET last_sent=$1 WHERE id=1", today_key)
                    finally:
                        await release_conn(conn)
                    asyncio.create_task(_send_daily_dms(
                        cfg["title"], cfg["message"], cfg["color"]))

        except Exception as e:
            print(f"[DAILY DM LOOP] Error: {e}")

        await asyncio.sleep(55)  # check every ~minute

@bot.tree.command(name="setdmupdate", description="[Admin] Configure the daily DM blast to all saved members.")
@app_commands.describe(
    hour="Hour to send (UTC, 0-23)",
    minute="Minute to send (0-59)",
    title="DM title",
    message="DM message body",
    color="Embed color: green, red, blue, gold, purple",
    enabled="Enable or disable the daily DM (yes/no)"
)
@admin_only()
async def cmd_setdmupdate(
    interaction: discord.Interaction,
    hour: int,
    minute: int,
    title: str,
    message: str,
    color: str = "gold",
    enabled: str = "yes"
):
    if not (0 <= hour <= 23) or not (0 <= minute <= 59):
        await interaction.response.send_message("❌ Hour must be 0-23, minute 0-59.", ephemeral=True)
        return

    is_enabled = enabled.lower() in ("yes", "y", "true", "1")
    conn = await get_conn()
    try:
        await _ensure_member_snapshot_table(conn)
        await conn.execute("""
            UPDATE daily_dm_config SET
                send_hour=$1, send_minute=$2, title=$3,
                message=$4, color=$5, enabled=$6
            WHERE id=1
        """, hour, minute, title, message, color, is_enabled)
    finally:
        await release_conn(conn)

    embed = discord.Embed(title="Daily DM Configured", color=C_GOLD)
    embed.add_field(name="⏰ Time",    value=f"`{hour:02d}:{minute:02d} UTC`", inline=True)
    embed.add_field(name="📌 Title",   value=title,                            inline=True)
    embed.add_field(name="🎨 Color",   value=color,                            inline=True)
    embed.add_field(name="✅ Enabled", value="Yes" if is_enabled else "No",    inline=True)
    embed.add_field(name="📝 Message", value=message[:500],                    inline=False)
    embed.set_footer(text=f"Set by {interaction.user} | {now_ts()}")
    await interaction.response.send_message(embed=embed, ephemeral=True)

@bot.tree.command(name="dmupdate", description="[Admin] Manually trigger the daily DM blast right now.")
@app_commands.describe(
    title="DM title",
    message="Message to send",
    color="Embed color: green, red, blue, gold, purple"
)
@admin_only()
async def cmd_dmupdate(
    interaction: discord.Interaction,
    title: str,
    message: str,
    color: str = "gold"
):
    await interaction.response.send_message(
        f"📤 Sending DM update to all saved members...", ephemeral=True)
    asyncio.create_task(_send_daily_dms(title, message, color))

@bot.tree.command(name="redeemmessagerewards", description="Claim your pending message milestone rewards (25M gems per 500 messages).")
async def cmd_redeemmessagerewards(interaction: discord.Interaction):
    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        await ensure_message_tables(conn)
        uid = str(interaction.user.id)
        row = await conn.fetchrow("SELECT total_count, unclaimed_miles, total_claimed FROM message_counts WHERE user_id=$1", uid)

        total     = row["total_count"]     if row else 0
        unclaimed = row["unclaimed_miles"] if row else 0

        if unclaimed <= 0:
            next_ms   = ((total // MESSAGE_REWARD_EVERY) + 1) * MESSAGE_REWARD_EVERY
            remaining = next_ms - total
            await interaction.response.send_message(
                f"❌ No pending message rewards.\n"
                f"You have **{total}** messages. **{remaining}** more until your next **💎 {format_amount(MESSAGE_REWARD_AMOUNT)} gem** reward!",
                ephemeral=True
            )
            return

        payout = unclaimed * MESSAGE_REWARD_AMOUNT
        await update_balance(conn, interaction.user.id, payout)
        await log_transaction(conn, interaction.user.id, "message_reward", payout,
                              f"Claimed {unclaimed} message milestone reward(s)")
        await conn.execute("""
            UPDATE message_counts
            SET unclaimed_miles = 0,
                total_claimed   = total_claimed + $1
            WHERE user_id = $2
        """, unclaimed, uid)

        row2      = await conn.fetchrow("SELECT total_count, total_claimed FROM message_counts WHERE user_id=$1", uid)
        total2    = row2["total_count"]    if row2 else unclaimed * MESSAGE_REWARD_EVERY
        claimed2  = row2["total_claimed"]  if row2 else unclaimed
        next_ms   = ((total2 // MESSAGE_REWARD_EVERY) + 1) * MESSAGE_REWARD_EVERY
        remaining = next_ms - total2

        embed = discord.Embed(
            color=C_WIN,
            description=(
                f"## 🎉  Message Rewards Claimed!\n"
                f"💎 **{format_amount(payout)} gems** added to your balance!\n\n"
                f"📝 **Total messages:** {total2:,}\n"
                f"🎁 **Milestones claimed:** {unclaimed}\n"
                f"⏳ **Next reward in:** {remaining} more messages"
            )
        )
        embed.set_thumbnail(url=await get_avatar(interaction.user))
        embed.set_footer(text="500 messages = 25M gems 💎  •  Keep chatting!")
        _brand_embed(embed)
        await interaction.response.send_message(embed=embed)

    except Exception as e:
        print(f"[ERROR] redeemmessagerewards: {type(e).__name__}: {e}")
        import traceback; traceback.print_exc()
        if interaction.response.is_done():
            await interaction.followup.send("⚠️  Something went wrong — try again.", ephemeral=True)
        else:
            await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
    finally:
        await release_conn(conn)

@bot.tree.command(name="messages", description="Check your message count and reward progress.")
async def cmd_messages(interaction: discord.Interaction):
    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        await ensure_message_tables(conn)
        uid = str(interaction.user.id)
        row = await conn.fetchrow("SELECT total_count, unclaimed_miles, total_claimed FROM message_counts WHERE user_id=$1", uid)

        total         = row["total_count"]     if row else 0
        unclaimed     = row["unclaimed_miles"] if row else 0
        total_claimed = row["total_claimed"]   if row else 0
        progress      = total % MESSAGE_REWARD_EVERY
        bar_filled    = int((progress / MESSAGE_REWARD_EVERY) * 10)
        bar           = "█" * bar_filled + "░" * (10 - bar_filled)
        next_ms       = ((total // MESSAGE_REWARD_EVERY) + 1) * MESSAGE_REWARD_EVERY
        remaining     = next_ms - total

        embed = discord.Embed(
            color=C_VIP,
            description=(
                f"## 💬  Message Stats\n"
                f"📝 **Total Messages:** {total:,}\n"
                f"💎 **Total Earned:** {format_amount(total_claimed * MESSAGE_REWARD_AMOUNT)} gems\n"
                f"⏳ **Pending Rewards:** {'None' if not unclaimed else f'{unclaimed}x = {format_amount(unclaimed * MESSAGE_REWARD_AMOUNT)} gems'}\n\n"
                f"**Progress to next reward:** {progress}/{MESSAGE_REWARD_EVERY}\n"
                f"`{bar}` — **{remaining}** messages to go"
            )
        )
        embed.set_thumbnail(url=await get_avatar(interaction.user))
        embed.set_footer(text="500 messages = 25M gems 💎  •  /redeemmessagerewards to claim")
        _brand_embed(embed)
        await interaction.response.send_message(embed=embed, ephemeral=True)

    except Exception as e:
        print(f"[ERROR] messages: {type(e).__name__}: {e}")
        if interaction.response.is_done():
            await interaction.followup.send("⚠️  Something went wrong — try again.", ephemeral=True)
        else:
            await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
    finally:
        await release_conn(conn)

CB_PLAYER_LUCK = 30   # player pull luck — biased toward common (low) rolls
CB_BOT_LUCK    = 72   # bot pull luck — biased toward rare (high) rolls, strong house edge

CASES = {
    "champion":    {"name": "Champion Case",      "emoji": "👑", "cost":    750_000_000, "color": 0xFFD700},
    "diamond_whale":{"name": "Diamond Whale Case","emoji": "💎", "cost":    550_000_000, "color": 0xB9F2FF},
    "legend":      {"name": "Legend Case",        "emoji": "🏆", "cost":    400_000_000, "color": 0xFFD700},
    "whale":       {"name": "Whale Case",         "emoji": "🐋", "cost":    300_000_000, "color": 0x1E90FF},
    "high_roller": {"name": "High Roller Case",   "emoji": "🎰", "cost":    225_000_000, "color": 0xFF6600},
    "emerald":     {"name": "Emerald Case",       "emoji": "💚", "cost":    175_000_000, "color": 0x50C878},
    "ruby":        {"name": "Ruby Case",          "emoji": "🔴", "cost":    125_000_000, "color": 0x9B111E},
    "platinum":    {"name": "Platinum Case",      "emoji": "💿", "cost":     80_000_000, "color": 0xE5E4E2},
    "gold":        {"name": "Gold Case",          "emoji": "🥇", "cost":     55_000_000, "color": 0xFFD700},
    "silver":      {"name": "Silver Case",        "emoji": "🥈", "cost":     38_000_000, "color": 0xC0C0C0},
    "bronze":      {"name": "Bronze Case",        "emoji": "🥉", "cost":     25_000_000, "color": 0xCD7F32},
}

CASE_PRIZES = {
    "champion": [
        (62,    525_000_000, "Champion Crumbs"),   # Common     — 0.70x (525M)
        (24,    637_500_000, "Crown Fragment"),     # Uncommon   — 0.85x (637.5M)
        (10,    937_500_000, "Champion Relic"),     # Legendary  — 1.25x (937.5M)
        ( 3,  2_625_000_000, "Hall of Champions"),  # Mythical   — 3.5x  (2.625B)
        ( 1,  3_750_000_000, "The Crown Jewel"),    # OG         — 5.0x  (3.75B)
    ],  # case cost = 750M
    "diamond_whale": [
        (62,    385_000_000, "Diamond Dust"),       # Common     — 0.70x (385M)
        (24,    467_500_000, "Whale Tooth"),         # Uncommon   — 0.85x (467.5M)
        (10,    687_500_000, "Diamond Vault"),       # Legendary  — 1.25x (687.5M)
        ( 3,  1_925_000_000, "Leviathan Drop"),      # Mythical   — 3.5x  (1.925B)
        ( 1,  2_750_000_000, "Diamond Genesis"),     # OG         — 5.0x  (2.75B)
    ],  # case cost = 550M
    "legend": [
        (62,    280_000_000, "Legend Scraps"),       # Common     — 0.70x (280M)
        (24,    340_000_000, "Crypto Vault"),         # Uncommon   — 0.85x (340M)
        (10,    500_000_000, "Legend Shard"),         # Legendary  — 1.25x (500M)
        ( 3,  1_400_000_000, "Hall of Fame Drop"),    # Mythical   — 3.5x  (1.4B)
        ( 1,  2_000_000_000, "Satoshi Throne"),       # OG         — 5.0x  (2B)
    ],  # case cost = 400M
    "whale": [
        (62,    210_000_000, "Whale Drip"),           # Common     — 0.70x (210M)
        (24,    255_000_000, "Deep Sea Chip"),         # Uncommon   — 0.85x (255M)
        (10,    375_000_000, "Leviathan Cache"),       # Legendary  — 1.25x (375M)
        ( 3,  1_050_000_000, "Whale Genesis"),         # Mythical   — 3.5x  (1.05B)
        ( 1,  1_500_000_000, "Ocean Throne"),          # OG         — 5.0x  (1.5B)
    ],  # case cost = 300M
    "high_roller": [
        (62,    157_500_000, "Table Crumbs"),          # Common     — 0.70x (157.5M)
        (24,    191_250_000, "Casino Chip"),            # Uncommon   — 0.85x (191.25M)
        (10,    281_250_000, "High Stakes Pot"),        # Legendary  — 1.25x (281.25M)
        ( 3,    787_500_000, "VIP Vault"),              # Mythical   — 3.5x  (787.5M)
        ( 1,  1_125_000_000, "The House Edge"),         # OG         — 5.0x  (1.125B)
    ],  # case cost = 225M
    "emerald": [
        (62,    122_500_000, "Green Dust"),             # Common     — 0.70x (122.5M)
        (24,    148_750_000, "Emerald Shard"),           # Uncommon   — 0.85x (148.75M)
        (10,    218_750_000, "Forest Vault"),            # Legendary  — 1.25x (218.75M)
        ( 3,    612_500_000, "Emerald Throne"),          # Mythical   — 3.5x  (612.5M)
        ( 1,    875_000_000, "Crown Jewel"),             # OG         — 5.0x  (875M)
    ],  # case cost = 175M
    "ruby": [
        (62,     87_500_000, "Blood Drop"),              # Common     — 0.70x (87.5M)
        (24,    106_250_000, "Ruby Shard"),               # Uncommon   — 0.85x (106.25M)
        (10,    156_250_000, "Crimson Vault"),             # Legendary  — 1.25x (156.25M)
        ( 3,    437_500_000, "Ruby Throne"),               # Mythical   — 3.5x  (437.5M)
        ( 1,    625_000_000, "Red Genesis"),               # OG         — 5.0x  (625M)
    ],  # case cost = 125M
    "platinum": [
        (62,     56_000_000, "Shiny Crumbs"),              # Common     — 0.70x (56M)
        (24,     68_000_000, "Platinum Dust"),              # Uncommon   — 0.85x (68M)
        (10,    100_000_000, "Steel Vault"),                # Legendary  — 1.25x (100M)
        ( 3,    280_000_000, "Platinum Relic"),             # Mythical   — 3.5x  (280M)
        ( 1,    400_000_000, "Platinum Genesis"),           # OG         — 5.0x  (400M)
    ],  # case cost = 80M
    "gold": [
        (62,     38_500_000, "Pocket Gold"),               # Common     — 0.70x (38.5M)
        (24,     46_750_000, "Gold Chip"),                  # Uncommon   — 0.85x (46.75M)
        (10,     68_750_000, "Gold Vault"),                 # Legendary  — 1.25x (68.75M)
        ( 3,    192_500_000, "Gold Throne"),                # Mythical   — 3.5x  (192.5M)
        ( 1,    275_000_000, "Gold Genesis"),               # OG         — 5.0x  (275M)
    ],  # case cost = 55M
    "silver": [
        (62,     26_600_000, "Spare Change"),               # Common     — 0.70x (26.6M)
        (24,     32_300_000, "Silver Dust"),                 # Uncommon   — 0.85x (32.3M)
        (10,     47_500_000, "Silver Vault"),                # Legendary  — 1.25x (47.5M)
        ( 3,    133_000_000, "Silver Throne"),               # Mythical   — 3.5x  (133M)
        ( 1,    190_000_000, "Silver Genesis"),              # OG         — 5.0x  (190M)
    ],  # case cost = 38M
    "bronze": [
        (62,     17_500_000, "Crumbs"),                      # Common     — 0.70x (17.5M)
        (24,     21_250_000, "Bronze Dust"),                  # Uncommon   — 0.85x (21.25M)
        (10,     31_250_000, "Bronze Vault"),                  # Legendary  — 1.25x (31.25M)
        ( 3,     87_500_000, "Bronze Throne"),                 # Mythical   — 3.5x  (87.5M)
        ( 1,    125_000_000, "Bronze Genesis"),                # OG         — 5.0x  (125M)
    ],  # case cost = 25M
}

PRIZE_TIER_EMOJIS  = ["⬜", "🟩", "🟣", "🔴", "🟡"]
PRIZE_TIER_LABELS  = ["Common", "Uncommon", "Legendary", "Mythical", "OG"]
MODE_PLAYER_COUNT  = {"1v1": 2, "1v1v1": 3, "2v2": 4}

def _roll_case(case_key: str, luck: int) -> tuple:
    """Shared roll logic. luck=0-100: 50=fair, 0=worst rolls, 100=best rolls.
    Returns (fixed_value, tier, item_name)."""
    prizes = CASE_PRIZES[case_key]
    n = len(prizes)
    wc = luck / 50.0
    weights = []
    for i, p in enumerate(prizes):
        tier_factor = 1.0 + (i / max(n - 1, 1) - 0.5) * (wc - 1.0) * 2
        weights.append(max(1, int(p[0] * max(0.05, tier_factor))))
    tier      = random.choices(range(n), weights=weights, k=1)[0]
    value     = prizes[tier][1]   # fixed value — no random range
    item_name = prizes[tier][2]
    return value, tier, item_name

def _open_case(case_key: str) -> tuple:
    """Open one case for a human — uses CB_PLAYER_LUCK (0-100)."""
    return _roll_case(case_key, CB_PLAYER_LUCK)

def _open_case_bot(case_key: str) -> tuple:
    """Open one case for a bot — uses CB_BOT_LUCK (0-100)."""
    return _roll_case(case_key, CB_BOT_LUCK)

async def _ensure_cb_tables(conn):
    await conn.execute("""
        CREATE TABLE IF NOT EXISTS case_battles (
            id          SERIAL PRIMARY KEY,
            creator_id  TEXT    NOT NULL,
            case_key    TEXT    NOT NULL,
            num_cases   INTEGER NOT NULL DEFAULT 1,
            num_players INTEGER NOT NULL DEFAULT 2,
            mode        TEXT    NOT NULL DEFAULT '1v1',
            entry_cost  BIGINT  NOT NULL DEFAULT 0,
            status      TEXT    NOT NULL DEFAULT 'open',
            message_id  TEXT,
            winner_ids  TEXT,
            created_at  TEXT    NOT NULL DEFAULT ''
        )
    """)
    await conn.execute("""
        CREATE TABLE IF NOT EXISTS case_battle_players (
            battle_id  INTEGER NOT NULL,
            user_id    TEXT    NOT NULL,
            is_bot     BOOLEAN NOT NULL DEFAULT FALSE,
            total_val  BIGINT  NOT NULL DEFAULT 0,
            joined_at  TEXT    NOT NULL DEFAULT '',
            PRIMARY KEY (battle_id, user_id)
        )
    """)

_CB_BOT_NAMES = [
    "Drake", "Rihanna", "Kanye", "Lil Wayne", "Cardi B",
    "Travis Scott", "Nicki Minaj", "Post Malone", "XXXTentacion", "Juice WRLD",
    "6ix9ine", "DaBaby", "Lil Baby", "Roddy Ricch", "Pop Smoke",
    "NBA YoungBoy", "Polo G", "Lil Durk", "Gunna", "Future",
    "Lil Uzi Vert", "Playboi Carti", "Tyler the Creator", "Kendrick Lamar", "J. Cole",
    "A$AP Rocky", "21 Savage", "Offset", "Quavo", "Takeoff",
    "Megan Thee Stallion", "Doja Cat", "Ice Spice", "Central Cee", "Skepta",
    "Dave", "Stormzy", "AJ Tracey", "Headie One", "Unknown T",
]

_cb_bot_name_cache: dict[int, dict[int, str]] = {}

def _cb_bot_name(battle_id: int, slot: int) -> str:
    """Return a stable celebrity name for a bot slot in a battle.
    Assigns once per (battle_id, slot) and caches it for consistency."""
    if battle_id not in _cb_bot_name_cache:
        _cb_bot_name_cache[battle_id] = {}
    cache = _cb_bot_name_cache[battle_id]
    if slot not in cache:
        used = set(cache.values())
        idx  = (battle_id * 7 + slot * 13) % len(_CB_BOT_NAMES)
        while _CB_BOT_NAMES[idx] in used:
            idx = (idx + 1) % len(_CB_BOT_NAMES)
        cache[slot] = _CB_BOT_NAMES[idx]
    return f"🤖 {cache[slot]}"

async def _get_battle_players(conn, battle_id: int, guild):
    """Return list of player dicts from DB, with stable bot names."""
    rows = await conn.fetch(
        "SELECT user_id, is_bot FROM case_battle_players WHERE battle_id=$1 ORDER BY joined_at",
        battle_id)
    players = []
    bot_slot = 0
    for r in rows:
        if r["is_bot"]:
            bname = _cb_bot_name(battle_id, bot_slot)
            bot_slot += 1
            players.append({
                "id": r["user_id"], "name": bname,
                "mention": f"**{bname}**", "is_bot": True, "member": None
            })
        else:
            m = guild.get_member(int(r["user_id"])) if guild else None
            players.append({
                "id":      r["user_id"],
                "name":    m.display_name if m else f"Player",
                "mention": m.mention if m else f"<@{r['user_id']}>",
                "is_bot":  False,
                "member":  m,
            })
    return players

class CaseBattleSetupView(discord.ui.View):
    """Ephemeral setup panel — creator picks case, mode, num_cases then confirms."""

    def __init__(self, creator: discord.Member):
        super().__init__(timeout=180)
        self.creator   = creator
        self.case_key  = None
        self.num_cases = 1
        self.mode      = "1v1"
        self._build_selects()

    def _build_selects(self):
        case_opts = [
            discord.SelectOption(
                label=f"{c['name']}  ·  {format_amount(c['cost'])} / case",
                value=k, emoji=c["emoji"],
                description=f"Top: {CASE_PRIZES[k][-1][2]}  {format_amount(CASE_PRIZES[k][-1][1])}"
            )
            for k, c in CASES.items()
        ]
        case_sel = discord.ui.Select(
            placeholder="🎁  Choose a case...",
            options=case_opts, row=0
        )
        case_sel.callback = self._on_case
        self.add_item(case_sel)

        mode_opts = [
            discord.SelectOption(label="1v1  — 2 players",  value="1v1",   emoji="⚔️",  description="Winner takes all"),
            discord.SelectOption(label="1v1v1 — 3 players", value="1v1v1", emoji="🔱",  description="Highest total wins"),
            discord.SelectOption(label="2v2  — 4 players",  value="2v2",   emoji="🤝",  description="Teams — best combined total wins"),
        ]
        mode_sel = discord.ui.Select(
            placeholder="👥  Choose battle mode...",
            options=mode_opts, row=1
        )
        mode_sel.callback = self._on_mode
        self.add_item(mode_sel)

    async def _on_case(self, interaction: discord.Interaction):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your panel.", ephemeral=True)
            return
        self.case_key = interaction.data["values"][0]
        await interaction.response.edit_message(embed=self._build_embed(), view=self)

    async def _on_mode(self, interaction: discord.Interaction):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your panel.", ephemeral=True)
            return
        self.mode = interaction.data["values"][0]
        await interaction.response.edit_message(embed=self._build_embed(), view=self)

    def _build_embed(self) -> discord.Embed:
        case = CASES.get(self.case_key)
        num_pl = MODE_PLAYER_COUNT[self.mode]
        entry = (case["cost"] * self.num_cases) if case else 0
        pot   = entry * num_pl

        case_str = f"{case['emoji']} {case['name']}" if case else "*not chosen*"
        lines = [
            f"{'✅' if self.case_key else '⬜'} **Case:** {case_str}",
            f"✅ **Mode:** `{self.mode}` ({num_pl} players)",
            f"✅ **Cases:** `{self.num_cases}` per player",
        ]
        if case:
            lines += [
                "",
                f"💰 **Entry:** {format_amount(entry)}",
                f"🏆 **Total Pot:** {format_amount(pot)}",
            ]

        e = discord.Embed(
            description="## ⚔️  CASE BATTLE\n" + "\n".join(lines),
            color=case["color"] if case else C_GOLD
        )
        e.set_footer(text="Only you can see this panel  ·  Expires in 3 minutes")
        return e

    @discord.ui.button(label="➕", style=discord.ButtonStyle.grey, row=2)
    async def btn_more(self, interaction: discord.Interaction, btn: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your panel.", ephemeral=True)
            return
        self.num_cases = min(self.num_cases + 1, 100)
        self._sync_labels()
        await interaction.response.edit_message(embed=self._build_embed(), view=self)

    @discord.ui.button(label="➖", style=discord.ButtonStyle.grey, row=2)
    async def btn_less(self, interaction: discord.Interaction, btn: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your panel.", ephemeral=True)
            return
        self.num_cases = max(self.num_cases - 1, 1)
        self._sync_labels()
        await interaction.response.edit_message(embed=self._build_embed(), view=self)

    @discord.ui.button(label="Cases: 1", style=discord.ButtonStyle.blurple, row=2, disabled=True)
    async def btn_count_display(self, interaction: discord.Interaction, btn: discord.ui.Button):
        await interaction.response.defer()

    def _sync_labels(self):
        for item in self.children:
            if isinstance(item, discord.ui.Button) and item.disabled:
                item.label = f"Cases: {self.num_cases}"

    async def on_timeout(self):
        """User closed the ephemeral panel without confirming — release their game session."""
        _end_game_session(self.creator.id)

    @discord.ui.button(label="✅  Confirm & Pay", style=discord.ButtonStyle.green, row=3)
    async def btn_confirm(self, interaction: discord.Interaction, btn: discord.ui.Button):
        if interaction.user.id != self.creator.id:
            await interaction.response.send_message("❌ Not your panel.", ephemeral=True)
            return
        if not self.case_key:
            await interaction.response.send_message("❌ Please choose a case first.", ephemeral=True)
            return

        case       = CASES[self.case_key]
        num_pl     = MODE_PLAYER_COUNT[self.mode]
        entry_cost = case["cost"] * self.num_cases

        conn = await get_conn()
        try:
            await _ensure_cb_tables(conn)
            await ensure_user(conn, interaction.user)

            async with get_user_lock(interaction.user.id):
                ok = await deduct_balance_safe(conn, interaction.user.id, entry_cost)
                if not ok:
                    row = await get_user(conn, interaction.user.id)
                    bal = row["balance"] if row else 0
                    await interaction.response.send_message(
                        f"❌ Need **{format_amount(entry_cost)}** — you only have **{format_amount(bal)}**.",
                        ephemeral=True)
                    return

            battle_id = await conn.fetchval(
                """INSERT INTO case_battles
                   (creator_id, case_key, num_cases, num_players, mode, entry_cost, status, created_at)
                   VALUES ($1,$2,$3,$4,$5,$6,'open',$7) RETURNING id""",
                str(interaction.user.id), self.case_key, self.num_cases,
                num_pl, self.mode, entry_cost, now_ts()
            )
            await conn.execute(
                "INSERT INTO case_battle_players (battle_id,user_id,is_bot,joined_at) VALUES ($1,$2,FALSE,$3)",
                battle_id, str(interaction.user.id), now_ts()
            )
            await log_transaction(conn, interaction.user.id, "casebattle_entry",
                                  -entry_cost, f"battle #{battle_id}")
            players = await _get_battle_players(conn, battle_id, interaction.guild)
        except Exception as e:
            print(f"[CB CONFIRM] Error: {e}")
            await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
            return
        finally:
            await release_conn(conn)

        _end_game_session(interaction.user.id)
        self.stop()

        lobby_view = CaseBattleLobbyView(
            battle_id=battle_id, creator=interaction.user,
            case_key=self.case_key, num_cases=self.num_cases,
            mode=self.mode, num_players=num_pl, entry_cost=entry_cost,
        )
        lobby_embed = lobby_view.build_embed(players)

        try:
            conn2 = await get_conn()
            try:
                ch_row = await conn2.fetchrow("SELECT value FROM bot_settings WHERE key='casebattle_channel'")
            finally:
                await release_conn(conn2)
            target_ch = interaction.guild.get_channel(int(ch_row["value"])) if ch_row else None
        except Exception:
            target_ch = None
        if not target_ch:
            target_ch = interaction.channel

        lobby_msg = await target_ch.send(embed=lobby_embed, view=lobby_view)
        lobby_view.message = lobby_msg

        try:
            conn3 = await get_conn()
            try:
                await conn3.execute(
                    "UPDATE case_battles SET message_id=$1 WHERE id=$2",
                    str(lobby_msg.id), battle_id)
            finally:
                await release_conn(conn3)
        except Exception:
            pass

        await interaction.response.edit_message(
            embed=discord.Embed(
                color=C_WIN,
                description=f"## ⚔️  LOBBY OPEN\n[Jump to battle →]({lobby_msg.jump_url})"
            ),
            view=None
        )

        asyncio.create_task(_cb_timeout(battle_id, lobby_msg, lobby_view))

class CaseBattleLobbyView(discord.ui.View):

    def __init__(self, *, battle_id, creator, case_key, num_cases,
                 mode, num_players, entry_cost):
        super().__init__(timeout=None)   # _cb_timeout task handles expiry
        self.battle_id   = battle_id
        self.creator     = creator
        self.case_key    = case_key
        self.num_cases   = num_cases
        self.mode        = mode
        self.num_players = num_players
        self.entry_cost  = entry_cost
        self.message     = None
        self._lock       = asyncio.Lock()
        self.started     = False

    def build_embed(self, players: list) -> discord.Embed:
        c         = CASES[self.case_key]
        filled    = len(players)
        total_pot = self.entry_cost * self.num_players
        slots_left = self.num_players - filled

        roster = []
        for i, p in enumerate(players):
            icon = "👤" if not p["is_bot"] else "🤖"
            roster.append(f"`{i+1}.` {icon} {p['mention']}")
        for i in range(slots_left):
            roster.append(f"`{filled+i+1}.` ⬜ *Waiting...*")

        bar_filled = "█" * filled
        bar_empty  = "░" * slots_left
        progress   = f"`{bar_filled}{bar_empty}` {filled}/{self.num_players}"

        mode_labels = {"1v1": "⚔️ 1v1", "1v1v1": "🔱 1v1v1", "2v2": "🤝 2v2"}

        e = discord.Embed(
            color=c["color"],
            description=f"## ⚔️  CASE BATTLE  ·  Battle #{self.battle_id}"
        )
        e.add_field(name=f"{c['emoji']} Case",      value=f"**{c['name']}**",                       inline=True)
        e.add_field(name="📦 Cases Each",            value=f"**{self.num_cases}x**",                 inline=True)
        e.add_field(name="💰 Entry",                 value=f"**{format_amount(self.entry_cost)} 💎**",  inline=True)
        e.add_field(name="🏆 Prize Pool",            value=f"**{format_amount(total_pot)} 💎**",        inline=True)
        e.add_field(name="👥 Slots",                 value=progress,                                 inline=True)
        e.add_field(name="⏳ Expires",               value="5 minutes",                              inline=True)
        e.add_field(name="📋 Roster",                value="\n".join(roster),                        inline=False)

        if slots_left > 0:
            e.set_footer(text=f"Battle #{self.battle_id}  ·  {slots_left} slot{'s' if slots_left != 1 else ''} remaining  ·  Created by {self.creator.display_name}")
        else:
            e.set_footer(text=f"Battle #{self.battle_id}  ·  Full! Starting now...")
        return e

    @discord.ui.button(label="⚔️  Join Battle", style=discord.ButtonStyle.green, row=0)
    async def btn_join(self, interaction: discord.Interaction, btn: discord.ui.Button):
        async with self._lock:
            if self.started:
                await interaction.response.send_message("❌ This battle has already started.", ephemeral=True)
                return

            conn = await get_conn()
            try:
                await _ensure_cb_tables(conn)

                status_row = await conn.fetchrow("SELECT status FROM case_battles WHERE id=$1", self.battle_id)
                if not status_row or status_row["status"] != "open":
                    await interaction.response.send_message("❌ This battle is no longer open.", ephemeral=True)
                    return

                already = await conn.fetchrow(
                    "SELECT 1 FROM case_battle_players WHERE battle_id=$1 AND user_id=$2",
                    self.battle_id, str(interaction.user.id))
                if already:
                    await interaction.response.send_message("❌ You're already in this battle.", ephemeral=True)
                    return

                count = await conn.fetchval(
                    "SELECT COUNT(*) FROM case_battle_players WHERE battle_id=$1", self.battle_id)
                if count >= self.num_players:
                    await interaction.response.send_message("❌ Battle is full.", ephemeral=True)
                    return

                async with get_user_lock(interaction.user.id):
                    await ensure_user(conn, interaction.user)
                    ok = await deduct_balance_safe(conn, interaction.user.id, self.entry_cost)
                    if not ok:
                        row = await get_user(conn, interaction.user.id)
                        bal = row["balance"] if row else 0
                        await interaction.response.send_message(
                            f"❌ Need **{format_amount(self.entry_cost)}** — you only have **{format_amount(bal)}**.",
                            ephemeral=True)
                        return
                    await conn.execute(
                        "INSERT INTO case_battle_players (battle_id,user_id,is_bot,joined_at) VALUES ($1,$2,FALSE,$3)",
                        self.battle_id, str(interaction.user.id), now_ts())
                    await log_transaction(conn, interaction.user.id, "casebattle_entry",
                                          -self.entry_cost, f"battle #{self.battle_id}")

                players = await _get_battle_players(conn, self.battle_id, interaction.guild)
            except Exception as e:
                print(f"[CB JOIN] Error: {e}")
                await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
                return
            finally:
                await release_conn(conn)

            if len(players) >= self.num_players:
                self.started = True
                for item in self.children:
                    if isinstance(item, discord.ui.Button):
                        item.disabled = True
                await interaction.response.edit_message(embed=self.build_embed(players), view=self)
                self.stop()
                asyncio.create_task(_run_cb(
                    self.battle_id, self.message, self.case_key,
                    self.num_cases, self.num_players, self.entry_cost, self.mode,
                    players))
            else:
                await interaction.response.edit_message(embed=self.build_embed(players), view=self)

    @discord.ui.button(label="🤖  Call Bot", style=discord.ButtonStyle.grey, row=0)
    async def btn_bot(self, interaction: discord.Interaction, btn: discord.ui.Button):
        async with self._lock:
            if self.started:
                await interaction.response.send_message("❌ Battle already started.", ephemeral=True)
                return
            if interaction.user.id != self.creator.id:
                await interaction.response.send_message("❌ Only the battle creator can call a bot.", ephemeral=True)
                return

            conn = await get_conn()
            try:
                await _ensure_cb_tables(conn)

                status_row = await conn.fetchrow("SELECT status FROM case_battles WHERE id=$1", self.battle_id)
                if not status_row or status_row["status"] != "open":
                    await interaction.response.send_message("❌ This battle is no longer open.", ephemeral=True)
                    return

                count = await conn.fetchval(
                    "SELECT COUNT(*) FROM case_battle_players WHERE battle_id=$1", self.battle_id)
                if count >= self.num_players:
                    await interaction.response.send_message("❌ Battle is already full.", ephemeral=True)
                    return

                slots_to_fill = self.num_players - count
                for i in range(slots_to_fill):
                    bot_uid = f"bot_{self.battle_id}_{count + i}"
                    await conn.execute(
                        "INSERT INTO case_battle_players (battle_id,user_id,is_bot,joined_at) VALUES ($1,$2,TRUE,$3)",
                        self.battle_id, bot_uid, now_ts())

                players = await _get_battle_players(conn, self.battle_id, interaction.guild)
            except Exception as e:
                print(f"[CB BOT] Error: {e}")
                await interaction.response.send_message("⚠️  Something went wrong — try again.", ephemeral=True)
                return
            finally:
                await release_conn(conn)

            if len(players) >= self.num_players:
                self.started = True
                for item in self.children:
                    if isinstance(item, discord.ui.Button):
                        item.disabled = True
                await interaction.response.edit_message(embed=self.build_embed(players), view=self)
                self.stop()
                asyncio.create_task(_run_cb(
                    self.battle_id, self.message, self.case_key,
                    self.num_cases, self.num_players, self.entry_cost, self.mode,
                    players))
            else:
                await interaction.response.edit_message(embed=self.build_embed(players), view=self)

async def _run_cb(battle_id, message, case_key, num_cases,
                  num_players, entry_cost, mode, players):
    """Animate case opens then resolve the winner."""
    case = CASES[case_key]
    pot  = entry_cost * num_players

    player_names = "  vs  ".join(p["name"][:16] for p in players)
    for countdown in [3, 2, 1]:
        bars = "█" * (4 - countdown) + "░" * (countdown - 1)
        cd_embed = discord.Embed(
            title=f"⏳  STARTING IN {countdown}...",
            description=(
                f"```\n"
                f"  {player_names}\n"
                f"  {'─' * 28}\n"
                f"  {bars}  {'🔴' if countdown == 3 else '🟡' if countdown == 2 else '🟢'}\n"
                f"```"
            ),
            color=0xE74C3C if countdown == 3 else 0xE8B84B if countdown == 2 else 0x2ECC71
        )
        cd_embed.add_field(name="📦 Case",    value=f"{case['emoji']} {case['name']}",         inline=True)
        cd_embed.add_field(name="🎲 Cases",   value=f"**×{num_cases}**",                        inline=True)
        cd_embed.add_field(name="💰 Entry",   value=f"**{format_amount(entry_cost)} 💎**",      inline=True)
        cd_embed.set_footer(text=f"Battle #{battle_id}  ·  {mode.upper()}")
        try:
            await message.edit(embed=cd_embed, view=None)
        except Exception as e:
            print(f"[CB COUNTDOWN] {e}")
        await asyncio.sleep(1.0)

    go_embed = discord.Embed(
        title="🟢  LETS GO!",
        description=f"```\n  {'█' * 4}  Opening cases...\n```",
        color=0x2ECC71
    )
    try:
        await message.edit(embed=go_embed, view=None)
    except Exception:
        pass
    await asyncio.sleep(0.5)

    _forced_outcomes = {}  # player_id -> "win" | "lose"
    for p in players:
        if p["is_bot"]:
            continue
        try:
            uid = int(p["id"])
        except (ValueError, TypeError):
            continue
        forced = _force_result.pop(uid, None)
        if forced:
            _forced_outcomes[p["id"]] = forced

    results = {p["id"]: [] for p in players}
    for _ in range(num_cases):
        for p in players:
            if p["is_bot"]:
                results[p["id"]].append(_open_case_bot(case_key))
            else:
                results[p["id"]].append(_open_case(case_key))

    prizes = CASE_PRIZES[case_key]
    lo_val    = prizes[0][1]            # lowest tier fixed value
    lo_name   = prizes[0][2]
    hi_val    = prizes[-1][1]           # highest tier fixed value
    hi_name   = prizes[-1][2]
    for p in players:
        if p["id"] not in _forced_outcomes:
            continue
        force  = _forced_outcomes[p["id"]]
        others = [x for x in players if x["id"] != p["id"]]
        if not others:
            continue
        if force == "win":
            results[p["id"]] = [(hi_val, len(prizes) - 1, hi_name)] * num_cases
            for opp in others:
                results[opp["id"]] = [(lo_val, 0, lo_name)] * num_cases
        elif force == "lose":
            results[p["id"]] = [(lo_val, 0, lo_name)] * num_cases
            for opp in others:
                results[opp["id"]] = [(hi_val, len(prizes) - 1, hi_name)] * num_cases

    prizes       = CASE_PRIZES[case_key]
    spin_frames  = 10   # how many fake items flash before landing
    spin_delay   = 0.18 # seconds between spin frames
    reveal_delay = 0.9  # pause on the real result before next case

    def _spin_item():
        """Random prize from the pool for the spinning reel."""
        tier = random.choices(range(len(prizes)), weights=[p[0] for p in prizes], k=1)[0]
        val  = prizes[tier][1]
        name = prizes[tier][2]
        return val, tier, name

    def _reel_line(val, tier, name=None, spinning=True):
        """Single item line — ▶ arrow highlights the landing slot."""
        arrow  = "▶" if not spinning else " "
        label  = f"**{name or '???'}**  ·  {format_amount(val)} 💎  *{PRIZE_TIER_LABELS[tier]}*"
        return f"{arrow} {PRIZE_TIER_EMOJIS[tier]} {label}"

    def _player_field(pid, round_idx, reel_val=None, reel_tier=None, reel_name=None, spinning=True):
        """Build one player's embed field value for a given round."""
        lines = []
        for i in range(round_idx):
            v, t, n = results[pid][i]
            lines.append(f"{PRIZE_TIER_EMOJIS[t]} ~~{n}~~ `{format_amount(v)}`")
        if reel_val is not None:
            lines.append(_reel_line(reel_val, reel_tier, reel_name, spinning=spinning))
        done = sum(v for v, t, n in results[pid][:round_idx + (0 if spinning else 1)])
        if done:
            lines.append(f"**Total: {format_amount(done)}**")
        return "\n".join(lines) if lines else "\u200b"

    for round_idx in range(num_cases):
        for frame in range(spin_frames):
            embed = discord.Embed(
                title=f"🎰  OPENING CASE {round_idx + 1} / {num_cases}",
                description=f"{'█' * (frame + 1)}{'░' * (spin_frames - frame - 1)}  Spinning...",
                color=case["color"]
            )
            for p in players:
                sv, st, sn = _spin_item()
                embed.add_field(
                    name=f"{p['name'][:24]}",
                    value=_player_field(p["id"], round_idx, sv, st, sn, spinning=True),
                    inline=True
                )
            embed.set_footer(text=f"Battle #{battle_id}  ·  Round {round_idx + 1}/{num_cases}")
            try:
                await message.edit(embed=embed, view=None)
            except Exception as e:
                print(f"[CB SPIN] {e}")
            await asyncio.sleep(spin_delay)

        real_v, real_tier, real_n = results[list(results.keys())[0]][round_idx]  # peek for color accent
        reveal_color = [0x95A5A6, 0x3498DB, 0x9B59B6, 0xE74C3C, 0xFFD700][real_tier]

        embed = discord.Embed(
            title=f"🎯  CASE {round_idx + 1} LANDED",
            description=f"{'█' * spin_frames}  **Landed!**",
            color=reveal_color
        )
        for p in players:
            embed.add_field(
                name=f"{p['name'][:24]}",
                value=_player_field(p["id"], round_idx, *results[p["id"]][round_idx], spinning=False),
                inline=True
            )
        embed.set_footer(text=f"Battle #{battle_id}  ·  Round {round_idx + 1}/{num_cases}")
        try:
            await message.edit(embed=embed, view=None)
        except Exception as e:
            print(f"[CB REVEAL] {e}")
        await asyncio.sleep(reveal_delay)

    totals = {p["id"]: sum(v for v, t, n in results[p["id"]]) for p in players}

    if mode == "2v2":
        team_a, team_b = players[:2], players[2:]
        ta = sum(totals[p["id"]] for p in team_a)
        tb = sum(totals[p["id"]] for p in team_b)
        if ta > tb:
            winners, w_label = team_a, f"{team_a[0]['name']} & {team_a[1]['name']}"
        elif tb > ta:
            winners, w_label = team_b, f"{team_b[0]['name']} & {team_b[1]['name']}"
        else:
            winners, w_label = players, "TIE — Everyone splits"
    else:
        best    = max(totals.values())
        winners = [p for p in players if totals[p["id"]] == best]
        w_label = " & ".join(p["name"] for p in winners)

    total_items_value = sum(totals.values())
    share             = total_items_value // max(len(winners), 1)
    winner_ids_set    = {p["id"] for p in winners}

    conn = await get_conn()
    try:
        for p in players:
            await conn.execute(
                "UPDATE case_battle_players SET total_val=$1 WHERE battle_id=$2 AND user_id=$3",
                totals[p["id"]], battle_id, p["id"])

            if p["is_bot"]:
                continue
            try:
                uid = int(p["id"])
            except (ValueError, TypeError):
                continue

            if p["id"] in winner_ids_set:
                await apply_win_payout(conn, uid, share, entry_cost, "casebattle")
                await record_game(conn, uid, True, entry_cost, share, "casebattle")
                await conn.execute(
                    """INSERT INTO user_stats (user_id, cb_wins) VALUES ($1, 1)
                       ON CONFLICT (user_id) DO UPDATE SET cb_wins = user_stats.cb_wins + 1""",
                    str(uid)
                )
            else:
                await record_game(conn, uid, False, entry_cost, 0, "casebattle")

        await conn.execute(
            "UPDATE case_battles SET status='finished', winner_ids=$1 WHERE id=$2",
            ",".join(p["id"] for p in winners), battle_id)
    except Exception as e:
        print(f"[CB RESOLVE] DB error: {e}")
    finally:
        await release_conn(conn)

    sorted_players = sorted(players, key=lambda p: totals[p["id"]], reverse=True)
    pos_icons      = ["🥇", "🥈", "🥉", "4️⃣"]
    board_lines    = []
    for i, p in enumerate(sorted_players):
        is_winner = p["id"] in winner_ids_set
        crown     = " 👑" if is_winner else ""
        if num_cases <= 3:
            item_lines = [
                f"{PRIZE_TIER_EMOJIS[t]} {n} `{format_amount(v)}`"
                for v, t, n in results[p["id"]]
            ]
            items_str = "\n".join(item_lines)
        else:
            best_v, best_t, best_n = max(results[p["id"]], key=lambda x: x[0])
            items_str = f"{PRIZE_TIER_EMOJIS[best_t]} Best: **{best_n}** `{format_amount(best_v)}`"
        board_lines.append(
            f"{pos_icons[min(i, 3)]} {p['mention']}{crown}\n"
            f"{items_str}\n"
            f"┗ **{format_amount(totals[p['id']])}** total"
        )

    mode_labels  = {"1v1": "⚔️ 1v1", "1v1v1": "🔱 1v1v1", "2v2": "🤝 2v2"}
    result_embed = discord.Embed(
        color=C_WIN if len(winners) < len(players) else C_GOLD,
        description=(
            f"## ⚔️  BATTLE OVER  ·  {mode_labels.get(mode, mode).upper()}\n"
            f"### 🏆  {w_label} wins!\n"
            f"```diff\n"
            f"+ {format_amount(share)} payout\n"
            f"# {num_cases} case{'s' if num_cases > 1 else ''}  ·  {len(players)} players\n"
            f"```"
        )
    )
    result_embed.add_field(name="Scoreboard", value="\n\n".join(board_lines), inline=False)
    result_embed.add_field(name="Payout",      value=f"`{format_amount(share)} 💎`",            inline=True)
    result_embed.add_field(name="Item Value",  value=f"`{format_amount(total_items_value)} 💎`", inline=True)
    result_embed.add_field(name="Case",        value=f"{CASES[case_key]['emoji']} {CASES[case_key]['name']} ×{num_cases}", inline=True)
    result_embed.set_footer(text=f"Battle #{battle_id}  ·  {now_ts()}")

    try:
        await message.edit(embed=result_embed, view=None)
    except Exception as e:
        print(f"[CB FINAL] edit failed: {e}")

    for p in players:
        if not p["is_bot"]:
            try:
                _end_game_session(int(p["id"]))
            except Exception:
                pass

    _cb_bot_name_cache.pop(battle_id, None)

    log_e = discord.Embed(title="⚔️ Case Battle Resolved", color=C_GOLD)
    log_e.add_field(name="Battle",  value=f"#{battle_id}  ·  {mode}",     inline=True)
    log_e.add_field(name="Case",    value=f"{case['name']}  ×{num_cases}", inline=True)
    log_e.add_field(name="Items Total", value=format_amount(total_items_value), inline=True)
    log_e.add_field(name="Winner",      value=w_label,                                 inline=True)
    log_e.add_field(name="Payout",      value=format_amount(share),             inline=True)
    log_e.set_footer(text=now_ts())
    await send_finance_log(log_e)

async def _cb_timeout(battle_id: int, message, view: CaseBattleLobbyView):
    """Refund everyone if the lobby doesn't fill in 5 minutes.
    Single authoritative timeout — view.timeout=None so Discord doesn't also fire."""
    await asyncio.sleep(300)
    if view.started:
        return

    async with view._lock:
        if view.started:
            return
        view.started = True

    prows = []
    conn = await get_conn()
    try:
        row = await conn.fetchrow("SELECT status FROM case_battles WHERE id=$1", battle_id)
        if not row or row["status"] != "open":
            return
        await conn.execute("UPDATE case_battles SET status='expired' WHERE id=$1", battle_id)
        prows = await conn.fetch(
            "SELECT user_id, is_bot FROM case_battle_players WHERE battle_id=$1", battle_id)
        for p in prows:
            if not p["is_bot"]:
                try:
                    uid = int(p["user_id"])
                except (ValueError, TypeError):
                    continue
                await update_balance(conn, uid, view.entry_cost)
                await log_transaction(conn, uid, "casebattle_refund",
                                      view.entry_cost, f"battle #{battle_id} expired")
    except Exception as e:
        print(f"[CB TIMEOUT] Error: {e}")
    finally:
        await release_conn(conn)

    for p in prows:
        if not p["is_bot"]:
            try:
                _end_game_session(int(p["user_id"]))
            except Exception:
                pass

    _cb_bot_name_cache.pop(battle_id, None)

    try:
        exp = discord.Embed(
            color=C_PUSH,
            description="## ⚔️  BATTLE EXPIRED\n> Lobby closed — all entries refunded."
        )
        exp.set_footer(text=f"Battle #{battle_id}")
        await message.edit(embed=exp, view=None)
    except Exception:
        pass

@bot.tree.command(name="createcasebattle", description="Create a case battle and challenge others.")
async def cmd_createcasebattle(interaction: discord.Interaction):
    if is_game_locked("createcasebattle", interaction.user):
        await interaction.response.send_message(
            "🔒 **Case Battle** is currently locked to staff only.", ephemeral=True
        )
        return
    if not _start_game_session(interaction.user.id):
        await interaction.response.send_message("⏳ You already have an active game running! Finish it before starting a new one.", ephemeral=True)
        return
    setup_view = CaseBattleSetupView(interaction.user)
    await interaction.response.send_message(
        embed=setup_view._build_embed(),
        view=setup_view,
        ephemeral=True
    )

ACHIEVEMENTS = [
    {"id":"first_blood",    "emoji":"🩸", "name":"First Blood",        "desc":"Win your first game",                        "cat":"gambling", "check": lambda r,x: r["wins"] >= 1},
    {"id":"ten_wins",       "emoji":"🎯", "name":"Getting Warmed Up",  "desc":"Win 10 games",                               "cat":"gambling", "check": lambda r,x: r["wins"] >= 10},
    {"id":"hundred_wins",   "emoji":"💯", "name":"Century Club",       "desc":"Win 100 games",                              "cat":"gambling", "check": lambda r,x: r["wins"] >= 100},
    {"id":"thousand_wins",  "emoji":"🏅", "name":"Grinder",            "desc":"Win 1,000 games",                            "cat":"gambling", "check": lambda r,x: r["wins"] >= 1_000},
    {"id":"tenk_wins",      "emoji":"🌠", "name":"Veteran",            "desc":"Win 10,000 games",                           "cat":"gambling", "check": lambda r,x: r["wins"] >= 10_000},
    {"id":"100k_wins",      "emoji":"🔱", "name":"Immortal",           "desc":"Win 100,000 games",                          "cat":"gambling", "check": lambda r,x: r["wins"] >= 100_000},
    {"id":"streak_5",       "emoji":"🔥", "name":"On Fire",            "desc":"Reach a 5-game win streak",                  "cat":"gambling", "check": lambda r,x: r["max_streak"] >= 5},
    {"id":"streak_15",      "emoji":"⚡", "name":"Unstoppable",        "desc":"Reach a 15-game win streak",                 "cat":"gambling", "check": lambda r,x: r["max_streak"] >= 15},
    {"id":"streak_30",      "emoji":"🌩️","name":"Lightning Rod",       "desc":"Reach a 30-game win streak",                 "cat":"gambling", "check": lambda r,x: r["max_streak"] >= 30},
    {"id":"streak_50",      "emoji":"☄️", "name":"God Mode",           "desc":"Reach a 50-game win streak",                 "cat":"gambling", "check": lambda r,x: r["max_streak"] >= 50},
    {"id":"streak_100",     "emoji":"👁️", "name":"Unkillable",         "desc":"Reach a 100-game win streak",                "cat":"gambling", "check": lambda r,x: r["max_streak"] >= 100},
    {"id":"played_500",     "emoji":"🎲", "name":"Warming Up",         "desc":"Play 500 games total",                       "cat":"gambling", "check": lambda r,x: (r["wins"]+r["losses"]) >= 500},
    {"id":"played_5000",    "emoji":"🎮", "name":"Addicted",           "desc":"Play 5,000 games total",                     "cat":"gambling", "check": lambda r,x: (r["wins"]+r["losses"]) >= 5_000},
    {"id":"played_25000",   "emoji":"🕹️","name":"No Life",             "desc":"Play 25,000 games total",                    "cat":"gambling", "check": lambda r,x: (r["wins"]+r["losses"]) >= 25_000},
    {"id":"played_100000",  "emoji":"💀", "name":"Needs Help",         "desc":"Play 100,000 games total",                   "cat":"gambling", "check": lambda r,x: (r["wins"]+r["losses"]) >= 100_000},
    {"id":"comeback",       "emoji":"🔄", "name":"Comeback Kid",       "desc":"Win after losing 10 in a row",               "cat":"gambling", "check": lambda r,x: x.get("had_comeback", False)},
    {"id":"first_loss",     "emoji":"😬", "name":"Welcome to Sabpot",  "desc":"Lose your first game",                       "cat":"gambling", "check": lambda r,x: r["losses"] >= 1},
    {"id":"lose_500",       "emoji":"📉", "name":"Rough Patch",        "desc":"Lose 500 games total",                       "cat":"gambling", "check": lambda r,x: r["losses"] >= 500},
    {"id":"lose_5000",      "emoji":"💸", "name":"Chronic Loser",      "desc":"Lose 5,000 games total",                     "cat":"gambling", "check": lambda r,x: r["losses"] >= 5_000},
    {"id":"lose_streak_10", "emoji":"🥶", "name":"Ice Cold",           "desc":"Hit a 10-game loss streak",                  "cat":"gambling", "check": lambda r,x: x.get("worst_streak",0) >= 10},
    {"id":"lose_streak_20", "emoji":"💔", "name":"Cursed",             "desc":"Hit a 20-game loss streak",                  "cat":"gambling", "check": lambda r,x: x.get("worst_streak",0) >= 20},
    {"id":"lose_streak_50", "emoji":"☠️", "name":"Cooked",             "desc":"Hit a 50-game loss streak",                  "cat":"gambling", "check": lambda r,x: x.get("worst_streak",0) >= 50},
    {"id":"broke",          "emoji":"🪙", "name":"Going Broke",        "desc":"Hit 0 balance",                              "cat":"gambling", "check": lambda r,x: x.get("hit_zero", False)},
    {"id":"cf_win_1",       "emoji":"🪙", "name":"Heads or Tails",     "desc":"Win a coinflip",                             "cat":"games",    "check": lambda r,x: x.get("cf_wins",0) >= 1},
    {"id":"cf_win_250",     "emoji":"🌀", "name":"Flip Addict",        "desc":"Win 250 coinflips",                          "cat":"games",    "check": lambda r,x: x.get("cf_wins",0) >= 250},
    {"id":"cf_win_2500",    "emoji":"🏧", "name":"Flip God",           "desc":"Win 2,500 coinflips",                        "cat":"games",    "check": lambda r,x: x.get("cf_wins",0) >= 2_500},
    {"id":"dice_win_1",     "emoji":"🎲", "name":"Lucky Roll",         "desc":"Win a dice game",                            "cat":"games",    "check": lambda r,x: x.get("dice_wins",0) >= 1},
    {"id":"dice_win_500",   "emoji":"🎯", "name":"Dice Demon",         "desc":"Win 500 dice games",                         "cat":"games",    "check": lambda r,x: x.get("dice_wins",0) >= 500},
    {"id":"dice_win_5000",  "emoji":"🎳", "name":"Dice God",           "desc":"Win 5,000 dice games",                       "cat":"games",    "check": lambda r,x: x.get("dice_wins",0) >= 5_000},
    {"id":"bj_win_1",       "emoji":"♠️", "name":"21",                 "desc":"Win a blackjack hand",                       "cat":"games",    "check": lambda r,x: x.get("bj_wins",0) >= 1},
    {"id":"bj_win_250",     "emoji":"🃏", "name":"Card Shark",         "desc":"Win 250 blackjack hands",                    "cat":"games",    "check": lambda r,x: x.get("bj_wins",0) >= 250},
    {"id":"bj_win_2500",    "emoji":"🎴", "name":"House Beater",       "desc":"Win 2,500 blackjack hands",                  "cat":"games",    "check": lambda r,x: x.get("bj_wins",0) >= 2_500},
    {"id":"rlt_win_1",      "emoji":"◉",  "name":"Spin & Win",         "desc":"Win a roulette spin",                        "cat":"games",    "check": lambda r,x: x.get("rlt_wins",0) >= 1},
    {"id":"rlt_win_250",    "emoji":"🎡", "name":"Wheel Wizard",       "desc":"Win 250 roulette spins",                     "cat":"games",    "check": lambda r,x: x.get("rlt_wins",0) >= 250},
    {"id":"rlt_win_2500",   "emoji":"🌐", "name":"Roulette King",      "desc":"Win 2,500 roulette spins",                   "cat":"games",    "check": lambda r,x: x.get("rlt_wins",0) >= 2_500},
    {"id":"mines_clear_1",  "emoji":"💣", "name":"Defused",            "desc":"Clear a mines board",                        "cat":"games",    "check": lambda r,x: x.get("mines_clears",0) >= 1},
    {"id":"mines_clear_100","emoji":"🔰", "name":"Bomb Squad",         "desc":"Clear 100 mines boards",                     "cat":"games",    "check": lambda r,x: x.get("mines_clears",0) >= 100},
    {"id":"mines_clear_1000","emoji":"💥","name":"Minefield Walker",   "desc":"Clear 1,000 mines boards",                   "cat":"games",    "check": lambda r,x: x.get("mines_clears",0) >= 1_000},
    {"id":"mines_cashout",  "emoji":"💰", "name":"Cash Out King",      "desc":"Cash out of mines 250 times",                "cat":"games",    "check": lambda r,x: x.get("mines_cashouts",0) >= 250},
    {"id":"towers_clear_1", "emoji":"🗼", "name":"Tower Climber",      "desc":"Clear a towers board",                       "cat":"games",    "check": lambda r,x: x.get("towers_clears",0) >= 1},
    {"id":"towers_clear_100","emoji":"🏔️","name":"Summit Reached",     "desc":"Clear 100 towers boards",                    "cat":"games",    "check": lambda r,x: x.get("towers_clears",0) >= 100},
    {"id":"towers_clear_1000","emoji":"🌋","name":"Untouchable",        "desc":"Clear 1,000 towers boards",                  "cat":"games",    "check": lambda r,x: x.get("towers_clears",0) >= 1_000},
    {"id":"hilo_cashout_1", "emoji":"📈", "name":"Calculated",         "desc":"Cash out of HiLo with a profit",             "cat":"games",    "check": lambda r,x: x.get("hilo_cashouts",0) >= 1},
    {"id":"hilo_cashout_250","emoji":"🔮", "name":"Oracle",            "desc":"Cash out of HiLo 250 times",                 "cat":"games",    "check": lambda r,x: x.get("hilo_cashouts",0) >= 250},
    {"id":"rps_win_1",      "emoji":"✊", "name":"Challenger",         "desc":"Win an RPS game",                            "cat":"games",    "check": lambda r,x: x.get("rps_wins",0) >= 1},
    {"id":"rps_win_500",    "emoji":"✌️", "name":"RPS Legend",         "desc":"Win 500 RPS games",                          "cat":"games",    "check": lambda r,x: x.get("rps_wins",0) >= 500},
    {"id":"war_win_1",      "emoji":"⚔️","name":"Warrior",             "desc":"Win a war game",                             "cat":"games",    "check": lambda r,x: x.get("war_wins",0) >= 1},
    {"id":"war_win_500",    "emoji":"🛡️","name":"General",             "desc":"Win 500 war games",                          "cat":"games",    "check": lambda r,x: x.get("war_wins",0) >= 500},
    {"id":"baccarat_win_1", "emoji":"🎩", "name":"High Society",       "desc":"Win a baccarat game",                        "cat":"games",    "check": lambda r,x: x.get("baccarat_wins",0) >= 1},
    {"id":"baccarat_win_250","emoji":"🥂", "name":"James Bond",        "desc":"Win 250 baccarat games",                     "cat":"games",    "check": lambda r,x: x.get("baccarat_wins",0) >= 250},
    {"id":"scratch_win_1",  "emoji":"🎫", "name":"Lucky Ticket",       "desc":"Win a scratch card",                         "cat":"games",    "check": lambda r,x: x.get("scratch_wins",0) >= 1},
    {"id":"scratch_win_100","emoji":"🎰", "name":"Scratcher",          "desc":"Win 100 scratch cards",                      "cat":"games",    "check": lambda r,x: x.get("scratch_wins",0) >= 100},
    {"id":"horse_win_1",    "emoji":"🏇", "name":"Pick a Winner",      "desc":"Win a horse race bet",                       "cat":"games",    "check": lambda r,x: x.get("horse_wins",0) >= 1},
    {"id":"horse_win_250",  "emoji":"🏆", "name":"Jockey",             "desc":"Win 250 horse race bets",                    "cat":"games",    "check": lambda r,x: x.get("horse_wins",0) >= 250},
    {"id":"balloon_pop_1",  "emoji":"🎈", "name":"Pop!",               "desc":"Pop a balloon",                              "cat":"games",    "check": lambda r,x: x.get("balloon_pops",0) >= 1},
    {"id":"balloon_pop_250","emoji":"💥", "name":"Reckless",           "desc":"Pop 250 balloons",                           "cat":"games",    "check": lambda r,x: x.get("balloon_pops",0) >= 250},
    {"id":"balloon_cashout","emoji":"🪂", "name":"Know When to Stop",  "desc":"Cash out of balloon 100 times",              "cat":"games",    "check": lambda r,x: x.get("balloon_cashouts",0) >= 100},
    {"id":"upgrader_win_1", "emoji":"⬆️","name":"Upgraded",            "desc":"Win an upgrader bet",                        "cat":"games",    "check": lambda r,x: x.get("upgrader_wins",0) >= 1},
    {"id":"upgrader_win_100","emoji":"🚀","name":"To the Moon",        "desc":"Win 100 upgrader bets",                      "cat":"games",    "check": lambda r,x: x.get("upgrader_wins",0) >= 100},
    {"id":"cdice_win_1",    "emoji":"🎨", "name":"Color Me Lucky",     "desc":"Win a color dice game",                      "cat":"games",    "check": lambda r,x: x.get("cdice_wins",0) >= 1},
    {"id":"cdice_win_250",  "emoji":"🌈", "name":"Chromatic",          "desc":"Win 250 color dice games",                   "cat":"games",    "check": lambda r,x: x.get("cdice_wins",0) >= 250},
    {"id":"wager_10m",      "emoji":"💸", "name":"Getting Started",    "desc":"Wager 10M gems total",                       "cat":"economy",  "check": lambda r,x: r["wagered"] >= 10_000_000},
    {"id":"wager_50m",      "emoji":"💰", "name":"Warming Up",         "desc":"Wager 50M gems total",                       "cat":"economy",  "check": lambda r,x: r["wagered"] >= 50_000_000},
    {"id":"wager_200m",     "emoji":"🏦", "name":"High Roller",        "desc":"Wager 200M gems total",                      "cat":"economy",  "check": lambda r,x: r["wagered"] >= 200_000_000},
    {"id":"wager_600m",     "emoji":"🐋", "name":"Whale",              "desc":"Wager 600M gems total",                      "cat":"economy",  "check": lambda r,x: r["wagered"] >= 600_000_000},
    {"id":"wager_1b5",      "emoji":"🌊", "name":"Deep Water",         "desc":"Wager 1.5B gems total",                      "cat":"economy",  "check": lambda r,x: r["wagered"] >= 1_500_000_000},
    {"id":"wager_3b",       "emoji":"💎", "name":"Emerald",            "desc":"Wager 3B gems total",                        "cat":"economy",  "check": lambda r,x: r["wagered"] >= 3_000_000_000},
    {"id":"wager_5b",       "emoji":"🎰", "name":"Degenerate",         "desc":"Wager 5B gems total",                        "cat":"economy",  "check": lambda r,x: r["wagered"] >= 5_000_000_000},
    {"id":"wager_10b",      "emoji":"👑", "name":"Mega Whale",         "desc":"Wager 10B gems total",                       "cat":"economy",  "check": lambda r,x: r["wagered"] >= 10_000_000_000},
    {"id":"wager_15b",      "emoji":"🏴‍☠️","name":"Legend",             "desc":"Wager 15B gems total",                       "cat":"economy",  "check": lambda r,x: r["wagered"] >= 15_000_000_000},
    {"id":"balance_10m",    "emoji":"🔵", "name":"Stacking Up",        "desc":"Hold 10M gems at once",                      "cat":"economy",  "check": lambda r,x: r["balance"] >= 10_000_000},
    {"id":"balance_70m",    "emoji":"🟣", "name":"VIP Material",       "desc":"Hold 70M gems at once",                      "cat":"economy",  "check": lambda r,x: r["balance"] >= 70_000_000},
    {"id":"balance_500m",   "emoji":"💜", "name":"Rich",               "desc":"Hold 500M gems at once",                     "cat":"economy",  "check": lambda r,x: r["balance"] >= 500_000_000},
    {"id":"balance_2b",     "emoji":"🌟", "name":"Filthy Rich",        "desc":"Hold 2B gems at once",                       "cat":"economy",  "check": lambda r,x: r["balance"] >= 2_000_000_000},
    {"id":"balance_10b",    "emoji":"🏰", "name":"Empire",             "desc":"Hold 10B gems at once",                      "cat":"economy",  "check": lambda r,x: r["balance"] >= 10_000_000_000},
    {"id":"daily_7",        "emoji":"📅", "name":"Weekly",             "desc":"Claim daily 7 times",                        "cat":"economy",  "check": lambda r,x: x.get("daily_count",0) >= 7},
    {"id":"daily_30",       "emoji":"🗓️","name":"Monthly",             "desc":"Claim daily 30 times",                       "cat":"economy",  "check": lambda r,x: x.get("daily_count",0) >= 30},
    {"id":"daily_365",      "emoji":"🎂", "name":"Loyal",              "desc":"Claim daily 365 times",                      "cat":"economy",  "check": lambda r,x: x.get("daily_count",0) >= 365},
    {"id":"promo_redeem",   "emoji":"🎟️","name":"Code Breaker",        "desc":"Redeem a promo code",                        "cat":"economy",  "check": lambda r,x: x.get("promo_count",0) >= 1},
    {"id":"promo_10",       "emoji":"🗝️","name":"Hunter",              "desc":"Redeem 10 promo codes",                      "cat":"economy",  "check": lambda r,x: x.get("promo_count",0) >= 10},
    {"id":"big_single_win", "emoji":"💣", "name":"One Shot",           "desc":"Win 100M+ gems in a single game",            "cat":"economy",  "check": lambda r,x: x.get("biggest_win",0) >= 100_000_000},
    {"id":"godroll",        "emoji":"🌌", "name":"God Roll",           "desc":"Win 500M+ gems in a single game",            "cat":"economy",  "check": lambda r,x: x.get("biggest_win",0) >= 500_000_000},
    {"id":"sickroll",       "emoji":"🔴", "name":"Sick Roll",          "desc":"Win 1B+ gems in a single game",              "cat":"economy",  "check": lambda r,x: x.get("biggest_win",0) >= 1_000_000_000},
    {"id":"tip_once",       "emoji":"🤝", "name":"Generous",           "desc":"Send a tip to someone",                      "cat":"social",   "check": lambda r,x: r["tips_sent"] >= 1},
    {"id":"tip_50m",        "emoji":"💝", "name":"Philanthropist",     "desc":"Send 50M gems in tips total",                "cat":"social",   "check": lambda r,x: r["tips_sent"] >= 50_000_000},
    {"id":"tip_500m",       "emoji":"🫂", "name":"Big Spender",        "desc":"Send 500M gems in tips total",               "cat":"social",   "check": lambda r,x: r["tips_sent"] >= 500_000_000},
    {"id":"tip_recv_1",     "emoji":"🎁", "name":"Blessed",            "desc":"Receive a tip",                              "cat":"social",   "check": lambda r,x: r["tips_recv"] >= 1},
    {"id":"tip_recv_500m",  "emoji":"🤑", "name":"Popular",            "desc":"Receive 500M gems in tips total",            "cat":"social",   "check": lambda r,x: r["tips_recv"] >= 500_000_000},
    {"id":"rain_catch",     "emoji":"🌧️","name":"Rain Dancer",         "desc":"Catch a rain drop",                          "cat":"social",   "check": lambda r,x: x.get("rain_count",0) >= 1},
    {"id":"rain_catch_25",  "emoji":"⛈️","name":"Storm Chaser",        "desc":"Catch 25 rain drops",                        "cat":"social",   "check": lambda r,x: x.get("rain_count",0) >= 25},
    {"id":"rain_catch_100", "emoji":"🌊", "name":"Flood Survivor",     "desc":"Catch 100 rain drops",                       "cat":"social",   "check": lambda r,x: x.get("rain_count",0) >= 100},
    {"id":"cb_win",         "emoji":"⚔️","name":"Battle Tested",       "desc":"Win a case battle",                          "cat":"social",   "check": lambda r,x: x.get("cb_wins",0) >= 1},
    {"id":"cb_win_25",      "emoji":"🏆", "name":"Battle Hardened",    "desc":"Win 25 case battles",                        "cat":"social",   "check": lambda r,x: x.get("cb_wins",0) >= 25},
    {"id":"cb_win_100",     "emoji":"👹", "name":"Battle God",         "desc":"Win 100 case battles",                       "cat":"social",   "check": lambda r,x: x.get("cb_wins",0) >= 100},
]

if __name__ == "__main__":
    if not TOKEN:
        print("[BOT] ❌ No TOKEN set — add TOKEN to your environment variables.")
    else:
        bot.run(TOKEN)
