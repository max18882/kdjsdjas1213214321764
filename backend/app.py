import asyncio
import json
import mimetypes
import html
import os
import re
import socket
import sqlite3
import threading
import time
import traceback
import hashlib
import secrets
import smtplib
import ssl
from email.message import EmailMessage
from datetime import datetime, timezone, timedelta
from email.parser import BytesParser
from email.policy import default
from pathlib import Path
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse

try:
    from dotenv import load_dotenv
except Exception:
    def load_dotenv(path):
        path = Path(path)
        if not path.exists():
            return
        for line in path.read_text(encoding='utf-8', errors='ignore').splitlines():
            line = line.strip()
            if not line or line.startswith('#') or '=' not in line:
                continue
            key, value = line.split('=', 1)
            os.environ.setdefault(key.strip(), value.strip())

try:
    from telethon import TelegramClient
    from telethon.errors import (
        FloodWaitError,
        PhoneCodeExpiredError,
        PhoneCodeInvalidError,
        PhoneNumberInvalidError,
        PasswordHashInvalidError,
        SessionPasswordNeededError,
        RPCError,
    )
    from telethon.tl.types import Chat, Channel
except Exception as exc:
    print(f'[FATAL] Falha ao importar Telethon: {exc!r}', flush=True)
    raise

ROOT = Path(__file__).resolve().parent.parent
FRONTEND = ROOT / 'frontend'
DATA = ROOT / 'data'
SESSIONS = DATA / 'sessions'
MEDIA = DATA / 'media'
DB_PATH = DATA / 'app.db'
PORT_FILE = DATA / 'runtime_port.txt'
LOG_FILE = ROOT / 'backend.log'
ENV_FILE = ROOT / '.env'
HOST = '127.0.0.1'
AUTH_COOKIE = 'tp_session'
AUTH_SESSION_DAYS = 14

for folder in (DATA, SESSIONS, MEDIA):
    folder.mkdir(parents=True, exist_ok=True)
load_dotenv(ENV_FILE)

try:
    API_ID = int(os.getenv('TG_API_ID', '0') or '0')
except ValueError:
    API_ID = 0
API_HASH = os.getenv('TG_API_HASH', '').strip()

LOOP = None
HTTP_SERVER = None
SERVER_PORT = None
CLIENTS = {}          # account_id -> TelegramClient
PENDING = {}          # phone -> TelegramClient
STATE_LOCK = threading.RLock()


def log(*parts):
    msg = ' '.join(str(p) for p in parts)
    print(msg, flush=True)
    try:
        with LOG_FILE.open('a', encoding='utf-8') as fp:
            fp.write(msg + '\n')
    except Exception:
        pass


def utc_now():
    return datetime.now(timezone.utc)


def iso_now():
    return utc_now().isoformat()


def json_bytes(obj):
    return json.dumps(obj, ensure_ascii=False).encode('utf-8')


def db():
    conn = sqlite3.connect(DB_PATH, timeout=30)
    conn.row_factory = sqlite3.Row
    conn.execute('PRAGMA journal_mode=WAL')
    conn.execute('PRAGMA foreign_keys=ON')
    conn.execute('''
        CREATE TABLE IF NOT EXISTS accounts (
            id TEXT PRIMARY KEY,
            phone TEXT NOT NULL UNIQUE,
            title TEXT NOT NULL,
            username TEXT,
            created_at TEXT NOT NULL
        )
    ''')
    conn.execute('''
        CREATE TABLE IF NOT EXISTS jobs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id TEXT NOT NULL,
            chat_ids TEXT NOT NULL,
            text TEXT NOT NULL DEFAULT '',
            media_path TEXT,
            scheduled_at TEXT NOT NULL,
            status TEXT NOT NULL DEFAULT 'scheduled',
            created_at TEXT NOT NULL,
            repeat_minutes INTEGER DEFAULT NULL,
            sent_count INTEGER NOT NULL DEFAULT 0,
            last_sent_at TEXT
        )
    ''')
    # Migração silenciosa para bases criadas nas versões anteriores.
    columns = {row['name'] for row in conn.execute('PRAGMA table_info(jobs)').fetchall()}
    migrations = {
        'repeat_minutes': 'ALTER TABLE jobs ADD COLUMN repeat_minutes INTEGER DEFAULT NULL',
        'sent_count': 'ALTER TABLE jobs ADD COLUMN sent_count INTEGER NOT NULL DEFAULT 0',
        'last_sent_at': 'ALTER TABLE jobs ADD COLUMN last_sent_at TEXT',
    }
    for name, sql in migrations.items():
        if name not in columns:
            conn.execute(sql)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            email TEXT NOT NULL UNIQUE,
            password_hash TEXT NOT NULL,
            password_salt TEXT NOT NULL,
            email_verified INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL,
            last_login_at TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS email_verifications (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            code_hash TEXT NOT NULL,
            created_at TEXT NOT NULL,
            expires_at TEXT NOT NULL,
            attempts INTEGER NOT NULL DEFAULT 0,
            UNIQUE(user_id),
            FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS auth_sessions (
            token_hash TEXT PRIMARY KEY,
            user_id INTEGER NOT NULL,
            created_at TEXT NOT NULL,
            expires_at TEXT NOT NULL,
            FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE
        )
    """)
    conn.commit()
    return conn


def account_id_for(phone):
    digits = re.sub(r'\D', '', phone)
    return f'acct_{digits}'


def normalize_email(email):
    value = str(email or '').strip().lower()
    if not re.fullmatch(r"[^\s@]+@gmail\.com", value, re.I):
        raise ValueError('Digite um Gmail válido, por exemplo teste@gmail.com.')
    return value


def validate_password(password):
    password = str(password or '')
    if len(password) < 4:
        raise ValueError('A senha precisa ter pelo menos 4 caracteres.')
    return password


def hash_password(password, salt_hex=None):
    validate_password(password)
    salt = bytes.fromhex(salt_hex) if salt_hex else secrets.token_bytes(16)
    digest = hashlib.pbkdf2_hmac('sha256', password.encode('utf-8'), salt, 210_000)
    return digest.hex(), salt.hex()


def verify_password(password, digest_hex, salt_hex):
    try:
        digest = hashlib.pbkdf2_hmac('sha256', str(password).encode('utf-8'), bytes.fromhex(salt_hex), 210_000)
        return secrets.compare_digest(digest.hex(), digest_hex)
    except Exception:
        return False


def hash_code(code):
    return hashlib.sha256(str(code).encode('utf-8')).hexdigest()


def get_auth_user_from_token(token):
    token = str(token or '').strip()
    if not token:
        return None
    token_hash = hashlib.sha256(token.encode('utf-8')).hexdigest()
    conn = db()
    row = conn.execute(
        '''SELECT u.id, u.email, u.email_verified, u.created_at, u.last_login_at, s.expires_at
           FROM auth_sessions s JOIN users u ON u.id=s.user_id
           WHERE s.token_hash=?''',
        (token_hash,),
    ).fetchone()
    if not row:
        conn.close()
        return None
    try:
        expires = datetime.fromisoformat(row['expires_at'].replace('Z', '+00:00'))
    except Exception:
        expires = utc_now() - timedelta(seconds=1)
    if expires <= utc_now():
        conn.execute('DELETE FROM auth_sessions WHERE token_hash=?', (token_hash,))
        conn.commit(); conn.close()
        return None
    conn.close()
    return dict(row)


def issue_session(user_id):
    token = secrets.token_urlsafe(48)
    token_hash = hashlib.sha256(token.encode('utf-8')).hexdigest()
    now = utc_now()
    expires = now + timedelta(days=AUTH_SESSION_DAYS)
    conn = db()
    conn.execute('INSERT INTO auth_sessions(token_hash,user_id,created_at,expires_at) VALUES(?,?,?,?)',
                 (token_hash, user_id, now.isoformat(), expires.isoformat()))
    conn.execute('DELETE FROM auth_sessions WHERE expires_at <= ?', (now.isoformat(),))
    conn.commit(); conn.close()
    return token, expires


def send_verification_email(*args, **kwargs):
    return True


def current_user_from_request(handler):
    raw = handler.headers.get('Cookie', '')
    token = ''
    for item in raw.split(';'):
        if '=' not in item:
            continue
        key, value = item.strip().split('=', 1)
        if key == AUTH_COOKIE:
            token = value.strip()
            break
    return get_auth_user_from_token(token)


def require_config():
    if not API_ID or not API_HASH:
        raise RuntimeError('API do Telegram não configurada. Verifique o arquivo .env.')


def telegram_client(account_id):
    return TelegramClient(
        str(SESSIONS / account_id),
        API_ID,
        API_HASH,
        device_model='Telegram Poster',
        system_version='Windows',
        app_version='1.0',
    )


def get_client(account_id):
    with STATE_LOCK:
        client = CLIENTS.get(account_id)
    if not client:
        raise RuntimeError('Conta não conectada. Conecte a conta novamente.')
    if not client.is_connected():
        try:
            # Reconecta a sessão salva automaticamente para permitir recorrências longas.
            future = asyncio.run_coroutine_threadsafe(client.connect(), LOOP)
            future.result(timeout=35)
        except Exception as exc:
            raise RuntimeError(f'Não foi possível reconectar a conta: {exc}') from exc
    return client


def run_async(coro, timeout=120):
    if LOOP is None or not LOOP.is_running():
        raise RuntimeError('Motor do Telegram ainda não está pronto.')
    future = asyncio.run_coroutine_threadsafe(coro, LOOP)
    try:
        return future.result(timeout=timeout)
    except TimeoutError:
        future.cancel()
        raise RuntimeError('O Telegram demorou demais para responder.')


async def restore_accounts():
    conn = db()
    rows = conn.execute('SELECT id, phone FROM accounts ORDER BY created_at').fetchall()
    conn.close()
    for row in rows:
        aid = row['id']
        phone = row['phone']
        try:
            client = telegram_client(aid)
            await asyncio.wait_for(client.connect(), timeout=25)
            authorized = await asyncio.wait_for(client.is_user_authorized(), timeout=20)
            if authorized:
                with STATE_LOCK:
                    CLIENTS[aid] = client
                log(f'[OK] Conta restaurada: {phone}')
            else:
                await client.disconnect()
                log(f'[INFO] Sessão não autorizada: {phone}')
        except Exception as exc:
            log(f'[WARN] Falha restaurando {phone}: {exc}')


LINK_RE = re.compile(r"\[([^\]]+)\]\((https?://[^\s)]+|tg://[^\s)]+)\)")

def render_text_with_links(text):
    """Converte somente links no formato [texto](URL) em HTML seguro para o Telegram.

    Todo o restante do texto e escapado para evitar que caracteres < > & do usuario
    virem marcacao HTML acidental.
    """
    text = text or ''
    out = []
    cursor = 0
    for match in LINK_RE.finditer(text):
        out.append(html.escape(text[cursor:match.start()]))
        label = html.escape(match.group(1))
        url = html.escape(match.group(2), quote=True)
        out.append(f'<a href="{url}">{label}</a>')
        cursor = match.end()
    out.append(html.escape(text[cursor:]))
    return ''.join(out)


async def send_job(job):
    client = get_client(job['account_id'])
    chat_ids = json.loads(job['chat_ids'])
    media_path = job['media_path']
    text = job['text'] or ''
    formatted_text = render_text_with_links(text)

    successes = 0
    failures = []

    for index, chat_id in enumerate(chat_ids):
        try:
            if media_path:
                await client.send_file(
                    int(chat_id),
                    media_path,
                    caption=formatted_text or None,
                    parse_mode='html',
                )
            else:
                await client.send_message(
                    int(chat_id),
                    formatted_text,
                    parse_mode='html',
                )
            successes += 1
        except FloodWaitError as exc:
            wait_seconds = max(1, min(int(exc.seconds), 900))
            log(f'[FLOOD WAIT] Post #{job["id"]} chat {chat_id}: aguardando {wait_seconds}s.')
            await asyncio.sleep(wait_seconds)
            try:
                if media_path:
                    await client.send_file(
                        int(chat_id),
                        media_path,
                        caption=formatted_text or None,
                        parse_mode='html',
                    )
                else:
                    await client.send_message(
                        int(chat_id),
                        formatted_text,
                        parse_mode='html',
                    )
                successes += 1
            except Exception as retry_exc:
                failures.append(f'{chat_id}: {retry_exc}')
        except Exception as exc:
            failures.append(f'{chat_id}: {exc}')

        if index < len(chat_ids) - 1:
            await asyncio.sleep(1.2)

    if failures:
        log(f'[POST PARTIAL] #{job["id"]}: {successes} enviados, {len(failures)} falharam: {" | ".join(failures[:5])}')
    return successes, failures


async def scheduler_loop():
    """Executa posts agendados e recorrentes sem encerrar a recorrência por um erro isolado."""
    while True:
        try:
            conn = db()
            rows = conn.execute(
                "SELECT * FROM jobs WHERE status='scheduled' AND scheduled_at <= ? ORDER BY id",
                (iso_now(),),
            ).fetchall()
            conn.close()

            for row in rows:
                try:
                    successes, failures = await send_job(row)
                    now = utc_now()
                    repeat_minutes = int(row['repeat_minutes'] or 0)
                    conn = db()

                    if repeat_minutes > 0:
                        next_dt = now.replace(microsecond=0) + timedelta(minutes=repeat_minutes)
                        conn.execute(
                            "UPDATE jobs SET scheduled_at=?, sent_count=sent_count+?, last_sent_at=?, status='scheduled' WHERE id=?",
                            (next_dt.isoformat(), successes, now.isoformat(), row['id']),
                        )
                        conn.commit()
                        conn.close()
                        if failures:
                            log(f'[REPEAT PARTIAL] #{row["id"]}: {successes} enviados; próximo em {repeat_minutes} min.')
                        else:
                            log(f'[REPEAT OK] #{row["id"]}: {successes} enviados; próximo em {repeat_minutes} min.')
                    else:
                        conn.execute(
                            "UPDATE jobs SET status='sent', sent_count=sent_count+?, last_sent_at=? WHERE id=? AND status='scheduled'",
                            (successes, now.isoformat(), row['id']),
                        )
                        conn.commit()
                        conn.close()
                        log(f'[JOB OK] Post #{row["id"]}: {successes} enviados.')
                except Exception as exc:
                    repeat_minutes = int(row['repeat_minutes'] or 0)
                    conn = db()
                    now = utc_now()
                    if repeat_minutes > 0:
                        next_dt = now.replace(microsecond=0) + timedelta(minutes=max(1, repeat_minutes))
                        conn.execute(
                            "UPDATE jobs SET status='scheduled', scheduled_at=? WHERE id=?",
                            (next_dt.isoformat(), row['id']),
                        )
                    else:
                        conn.execute(
                            "UPDATE jobs SET status=? WHERE id=? AND status='scheduled'",
                            (f'error: {str(exc)[:220]}', row['id']),
                        )
                    conn.commit()
                    conn.close()
                    log(f'[JOB ERROR] #{row["id"]}: {exc}')
        except Exception as exc:
            log('[SCHEDULER ERROR]', repr(exc))
        await asyncio.sleep(2)


def parse_content_disposition(value):
    match = re.search(r'name="([^"]+)"', value or '')
    filename = re.search(r'filename="([^"]*)"', value or '')
    return (match.group(1) if match else None, Path(filename.group(1)).name if filename else None)


def parse_multipart(body, content_type):
    boundary_match = re.search(r'boundary=(?:"([^"]+)"|([^;]+))', content_type or '', flags=re.I)
    if not boundary_match:
        raise ValueError('multipart sem boundary')
    boundary = (boundary_match.group(1) or boundary_match.group(2)).strip().encode()
    parts = body.split(b'--' + boundary)
    result = {}
    for part in parts:
        part = part.strip(b'\r\n-')
        if not part:
            continue
        head, sep, data = part.partition(b'\r\n\r\n')
        if not sep:
            continue
        headers = BytesParser(policy=default).parsebytes(head + b'\r\n\r\n')
        name, filename = parse_content_disposition(headers.get('Content-Disposition', ''))
        if not name:
            continue
        data = data.rstrip(b'\r\n')
        result[name] = (filename or 'upload.bin', data) if filename is not None else data.decode('utf-8', 'ignore')
    return result


def safe_media_path(path_text):
    if not path_text:
        return None
    p = Path(path_text).resolve()
    root = MEDIA.resolve()
    if p == root or root not in p.parents or not p.is_file():
        raise ValueError('Arquivo de mídia inválido.')
    return p


def safe_frontend_path(url_path):
    rel = url_path.lstrip('/') or 'index.html'
    target = (FRONTEND / rel).resolve()
    root = FRONTEND.resolve()
    if root not in target.parents and target != root:
        return FRONTEND / 'index.html'
    if not target.is_file():
        return FRONTEND / 'index.html'
    return target


class Handler(BaseHTTPRequestHandler):
    protocol_version = 'HTTP/1.1'

    def log_message(self, fmt, *args):
        log('[HTTP]', fmt % args)

    def _send(self, status, payload, content_type='application/json; charset=utf-8', set_cookie=None, clear_cookie=False):
        data = payload if isinstance(payload, bytes) else json_bytes(payload)
        self.send_response(status)
        self.send_header('Content-Type', content_type)
        self.send_header('Content-Length', str(len(data)))
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Access-Control-Allow-Origin', 'http://127.0.0.1')
        self.send_header('Access-Control-Allow-Headers', 'Content-Type')
        self.send_header('Access-Control-Allow-Methods', 'GET,POST,DELETE,OPTIONS')
        if set_cookie:
            self.send_header('Set-Cookie', f'{AUTH_COOKIE}={set_cookie}; Max-Age=1209600; Path=/; HttpOnly; SameSite=Lax')
        elif clear_cookie:
            self.send_header('Set-Cookie', f'{AUTH_COOKIE}=; Max-Age=0; Path=/; HttpOnly; SameSite=Lax')
        self.end_headers()
        try:
            self.wfile.write(data)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _error(self, code, message):
        self._send(code, {'detail': message})

    def _body(self, limit=50 * 1024 * 1024):
        try:
            length = int(self.headers.get('Content-Length', '0'))
        except ValueError:
            raise ValueError('Content-Length inválido')
        if length < 0 or length > limit:
            raise ValueError('Arquivo muito grande. Limite: 50 MB.')
        return self.rfile.read(length)

    def _json(self):
        raw = self._body(2 * 1024 * 1024)
        if not raw:
            return {}
        return json.loads(raw.decode('utf-8'))

    def _user(self):
        return current_user_from_request(self)

    def _require_auth(self):
        user = self._user()
        if not user:
            self._error(401, 'Faça login para continuar.')
            return None
        return user

    def do_OPTIONS(self):
        self._send(204, b'', 'text/plain; charset=utf-8')

    def do_GET(self):
        try:
            path = urlparse(self.path).path
            if path == '/api/auth/me':
                user = self._user()
                return self._send(200, {'authenticated': bool(user), 'user': ({'id': user['id'], 'email': user['email']} if user else None)})
            if path == '/api/health':
                with STATE_LOCK:
                    connected = len(CLIENTS)
                return self._send(200, {
                    'ok': True,
                    'telegram_configured': bool(API_ID and API_HASH),
                    'connected_accounts': connected,
                    'port': SERVER_PORT,
                })

            if path == '/api/accounts':
                if not self._require_auth(): return
                conn = db()
                rows = conn.execute('SELECT * FROM accounts ORDER BY created_at').fetchall()
                conn.close()
                out = []
                for row in rows:
                    item = dict(row)
                    with STATE_LOCK:
                        item['connected'] = bool(CLIENTS.get(row['id']) and CLIENTS[row['id']].is_connected())
                    out.append(item)
                return self._send(200, out)

            match = re.fullmatch(r'/api/accounts/([^/]+)/chats', path)
            if match:
                if not self._require_auth(): return
                account_id = match.group(1)
                client = get_client(account_id)

                async def dialogs():
                    result = []
                    async for dialog in client.iter_dialogs():
                        entity = dialog.entity
                        is_group = isinstance(entity, Chat) or (
                            isinstance(entity, Channel) and bool(getattr(entity, 'megagroup', False))
                        )
                        if not is_group:
                            continue
                        result.append({
                            'id': int(dialog.id),
                            'title': dialog.name or 'Sem nome',
                            'username': getattr(entity, 'username', None),
                            'unread': int(dialog.unread_count or 0),
                        })
                    result.sort(key=lambda x: x['title'].lower())
                    return result

                return self._send(200, run_async(dialogs(), 120))

            if path == '/api/posts':
                if not self._require_auth(): return
                conn = db()
                rows = [dict(x) for x in conn.execute('SELECT * FROM jobs ORDER BY scheduled_at DESC LIMIT 500').fetchall()]
                conn.close()
                return self._send(200, rows)

            if path.startswith('/api/'):
                return self._error(404, 'Rota não encontrada')

            file_path = safe_frontend_path(path)
            data = file_path.read_bytes()
            content_type = mimetypes.guess_type(str(file_path))[0] or 'application/octet-stream'
            if file_path.suffix == '.js':
                content_type = 'application/javascript; charset=utf-8'
            elif file_path.suffix == '.css':
                content_type = 'text/css; charset=utf-8'
            elif file_path.suffix == '.html':
                content_type = 'text/html; charset=utf-8'
            return self._send(200, data, content_type)
        except Exception as exc:
            log('[GET ERROR]', repr(exc))
            return self._error(500, str(exc))

    def do_POST(self):
        try:
            path = urlparse(self.path).path

            if path == '/api/auth/register':
                body = self._json()
                email = normalize_email(body.get('email'))
                password = body.get('password', '')
                confirm = body.get('confirm_password')
                if confirm is not None and password != confirm:
                    raise ValueError('As senhas não são iguais.')
                validate_password(password)
                conn = db()
                exists = conn.execute('SELECT id FROM users WHERE email=?', (email,)).fetchone()
                if exists:
                    conn.close()
                    raise ValueError('Este e-mail já está cadastrado.')
                digest, salt = hash_password(password)
                now = iso_now()
                cur = conn.execute(
                    'INSERT INTO users(email,password_hash,password_salt,email_verified,created_at,last_login_at) VALUES(?,?,?,?,?,?)',
                    (email,digest,salt,1,now,now)
                )
                conn.commit()
                user_id = cur.lastrowid
                conn.close()
                token, _ = issue_session(user_id)
                self._set_cookie(token)
                return self._send(200, {'ok': True, 'user': {'id': user_id, 'email': email}, 'message': 'Conta criada com sucesso.'})

            if path == '/api/auth/login':
                body = self._json()
                try:
                    email = normalize_email(body.get('email'))
                except ValueError as exc:
                    return self._error(400, str(exc))
                password = str(body.get('password') or '')
                conn = db(); user = conn.execute('SELECT * FROM users WHERE email=?', (email,)).fetchone(); conn.close()
                if not user or not verify_password(password, user['password_hash'], user['password_salt']):
                    return self._error(401, 'E-mail ou senha incorretos.')
                token, _ = issue_session(user['id'])
                conn = db(); conn.execute('UPDATE users SET last_login_at=? WHERE id=?', (iso_now(), user['id'])); conn.commit(); conn.close()
                return self._send(200, {'ok': True, 'user': {'id': user['id'], 'email': email}}, set_cookie=token)

            if path == '/api/auth/logout':
                raw = self.headers.get('Cookie', '')
                token = ''
                for item in raw.split(';'):
                    if '=' in item:
                        key, value = item.strip().split('=', 1)
                        if key == AUTH_COOKIE:
                            token = value.strip(); break
                if token:
                    conn = db(); conn.execute('DELETE FROM auth_sessions WHERE token_hash=?', (hashlib.sha256(token.encode()).hexdigest(),)); conn.commit(); conn.close()
                return self._send(200, {'ok': True}, clear_cookie=True)

            if path == '/api/accounts/login/start':
                require_config()
                body = self._json()
                raw_phone = str(body.get('phone', '')).strip()
                phone = re.sub(r'\D', '', raw_phone)
                if not (8 <= len(phone) <= 15):
                    return self._error(400, 'Número inválido. Use o formato internacional, por exemplo +5511999999999.')

                phone = '+' + phone
                account_id = account_id_for(phone)
                with STATE_LOCK:
                    previous = PENDING.pop(phone, None)
                if previous:
                    try:
                        awaitable = previous.disconnect()
                        run_async(awaitable, 15)
                    except Exception:
                        pass

                async def begin_login():
                    client = telegram_client(account_id)
                    await asyncio.wait_for(client.connect(), 30)
                    if await asyncio.wait_for(client.is_user_authorized(), 20):
                        me = await client.get_me()
                        return {'already': True, 'client': client, 'me': me}
                    await asyncio.wait_for(client.send_code_request(phone), 30)
                    return {'already': False, 'client': client}

                try:
                    result = run_async(begin_login(), 70)
                except PhoneNumberInvalidError:
                    return self._error(400, 'O Telegram recusou esse número de telefone.')
                except FloodWaitError as exc:
                    return self._error(429, f'Tente novamente em {exc.seconds} segundos.')

                if result.get('already'):
                    client = result['client']
                    me = result['me']
                    title = ((me.first_name or '') + ((' ' + me.last_name) if me.last_name else '')).strip() or phone
                    with STATE_LOCK:
                        CLIENTS[account_id] = client
                    conn = db()
                    conn.execute(
                        'INSERT OR REPLACE INTO accounts(id,phone,title,username,created_at) VALUES(?,?,?,?,?)',
                        (account_id, phone, title, me.username or '', iso_now()),
                    )
                    conn.commit()
                    conn.close()
                    return self._send(200, {'ok': True, 'already_connected': True})

                with STATE_LOCK:
                    PENDING[phone] = result['client']
                return self._send(200, {'ok': True, 'message': 'Código enviado pelo Telegram.'})

            if path == '/api/accounts/login/verify':
                if not self._require_auth(): return
                require_config()
                body = self._json()
                phone = '+' + re.sub(r'\D', '', str(body.get('phone', '')).strip())
                code = re.sub(r'\D', '', str(body.get('code', '')).strip())
                password = body.get('password')
                with STATE_LOCK:
                    client = PENDING.get(phone)
                if not client:
                    return self._error(400, 'Login expirado. Clique em conectar novamente e peça um novo código.')
                account_id = account_id_for(phone)

                async def verify():
                    try:
                        await client.sign_in(phone=phone, code=code)
                    except SessionPasswordNeededError:
                        if not password:
                            return {'needs_2fa': True}
                        await client.sign_in(password=str(password))
                    me = await client.get_me()
                    title = ((me.first_name or '') + ((' ' + me.last_name) if me.last_name else '')).strip() or phone
                    return {'needs_2fa': False, 'title': title, 'username': me.username or ''}

                try:
                    result = run_async(verify(), 90)
                except PhoneCodeInvalidError:
                    return self._error(400, 'Código incorreto.')
                except PhoneCodeExpiredError:
                    return self._error(400, 'Código expirado. Solicite um novo código.')
                except PasswordHashInvalidError:
                    return self._error(400, 'Senha de duas etapas incorreta.')
                except FloodWaitError as exc:
                    return self._error(429, f'Tente novamente em {exc.seconds} segundos.')

                if result.get('needs_2fa'):
                    return self._send(200, {'ok': False, 'needs_2fa': True})

                with STATE_LOCK:
                    CLIENTS[account_id] = client
                    PENDING.pop(phone, None)
                conn = db()
                conn.execute(
                    'INSERT OR REPLACE INTO accounts(id,phone,title,username,created_at) VALUES(?,?,?,?,?)',
                    (account_id, phone, result['title'], result['username'], iso_now()),
                )
                conn.commit()
                conn.close()
                return self._send(200, {'ok': True, 'account_id': account_id, 'title': result['title'], 'username': result['username']})

            if path == '/api/shutdown':
                self._send(200, {'ok': True})
                threading.Thread(target=shutdown, daemon=True).start()
                return

            if path == '/api/media':
                if not self._require_auth(): return
                fields = parse_multipart(self._body(), self.headers.get('Content-Type', ''))
                item = fields.get('file')
                if not isinstance(item, tuple):
                    return self._error(400, 'Nenhum arquivo enviado.')
                filename, data = item
                if not data:
                    return self._error(400, 'Arquivo vazio.')
                if len(data) > 50 * 1024 * 1024:
                    return self._error(400, 'Arquivo maior que 50 MB.')
                filename = Path(filename).name or 'upload.bin'
                path = MEDIA / f'{int(time.time() * 1000)}_{filename}'
                path.write_bytes(data)
                return self._send(200, {'path': str(path), 'name': filename})

            if path == '/api/posts':
                if not self._require_auth(): return
                body = self._json()
                account_id = str(body.get('account_id') or '')
                chat_ids = body.get('chat_ids') or []
                text = str(body.get('text') or '')
                media_path = body.get('media_path')
                scheduled_at = str(body.get('scheduled_at') or '')
                try:
                    repeat_minutes = int(body.get('repeat_minutes') or 0)
                except (TypeError, ValueError):
                    return self._error(400, 'Intervalo de repetição inválido.')
                if repeat_minutes < 0:
                    return self._error(400, 'Intervalo de repetição inválido.')
                if 0 < repeat_minutes < 1:
                    return self._error(400, 'O intervalo mínimo é de 1 minuto.')
                if repeat_minutes > 24 * 60:
                    return self._error(400, 'O intervalo máximo é de 1440 minutos.')
                if not account_id or not chat_ids:
                    return self._error(400, 'Selecione uma conta e pelo menos um grupo.')
                if not text.strip() and not media_path:
                    return self._error(400, 'Escreva uma mensagem ou selecione uma mídia.')
                get_client(account_id)
                if media_path:
                    media_path = str(safe_media_path(media_path))
                try:
                    when = datetime.fromisoformat(scheduled_at.replace('Z', '+00:00'))
                except Exception:
                    return self._error(400, 'Data/hora inválida.')
                if when.tzinfo is None:
                    when = when.replace(tzinfo=timezone.utc)
                when = when.astimezone(timezone.utc)
                if when < utc_now():
                    when = utc_now()

                normalized_ids = []
                for item in chat_ids:
                    try:
                        normalized_ids.append(int(item))
                    except (TypeError, ValueError):
                        continue
                if not normalized_ids:
                    return self._error(400, 'Nenhum grupo válido foi selecionado.')

                conn = db()
                cur = conn.execute(
                    'INSERT INTO jobs(account_id,chat_ids,text,media_path,scheduled_at,status,created_at,repeat_minutes,sent_count,last_sent_at) VALUES(?,?,?,?,?,?,?,?,?,?)',
                    (
                        account_id,
                        json.dumps(normalized_ids),
                        text,
                        media_path,
                        when.isoformat(),
                        'scheduled',
                        iso_now(),
                        repeat_minutes or None,
                        0,
                        None,
                    ),
                )
                conn.commit()
                job_id = cur.lastrowid
                conn.close()
                return self._send(200, {
                    'ok': True,
                    'id': job_id,
                    'status': 'scheduled',
                    'repeat_minutes': repeat_minutes or None,
                })

            return self._error(404, 'Rota não encontrada')
        except json.JSONDecodeError:
            return self._error(400, 'JSON inválido.')
        except Exception as exc:
            log('[POST ERROR]', repr(exc))
            return self._error(500, str(exc))

    def do_DELETE(self):
        try:
            path = urlparse(self.path).path
            match = re.fullmatch(r'/api/accounts/([^/]+)', path)
            if match:
                if not self._require_auth(): return
                account_id = match.group(1)
                with STATE_LOCK:
                    client = CLIENTS.pop(account_id, None)
                if client:
                    try:
                        run_async(client.disconnect(), 20)
                    except Exception:
                        pass
                conn = db()
                conn.execute('DELETE FROM accounts WHERE id=?', (account_id,))
                conn.commit()
                conn.close()
                session_file = SESSIONS / account_id
                for suffix in ('.session', '.session-journal'):
                    try:
                        (Path(str(session_file) + suffix)).unlink(missing_ok=True)
                    except Exception:
                        pass
                return self._send(200, {'ok': True})

            match = re.fullmatch(r'/api/posts/(\d+)', path)
            if match:
                if not self._require_auth(): return
                conn = db()
                conn.execute("UPDATE jobs SET status='cancelled' WHERE id=? AND status='scheduled'", (int(match.group(1)),))
                conn.commit()
                conn.close()
                return self._send(200, {'ok': True})

            return self._error(404, 'Rota não encontrada')
        except Exception as exc:
            log('[DELETE ERROR]', repr(exc))
            return self._error(500, str(exc))


def pick_port():
    requested = int(os.getenv('TP_PORT', '0') or '0')
    candidates = [requested] if requested else list(range(8000, 8011))
    for port in candidates:
        if not port:
            continue
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            sock.bind((HOST, port))
            sock.close()
            return port
        except OSError:
            continue
    raise RuntimeError('Nenhuma porta livre entre 8000 e 8010.')


def shutdown():
    log('[INFO] Encerrando backend...')
    if HTTP_SERVER is not None:
        try:
            HTTP_SERVER.shutdown()
        except Exception:
            pass
    async def close_clients():
        with STATE_LOCK:
            all_clients = list(CLIENTS.values()) + list(PENDING.values())
            CLIENTS.clear()
            PENDING.clear()
        for client in all_clients:
            try:
                await client.disconnect()
            except Exception:
                pass
    if LOOP is not None and LOOP.is_running():
        try:
            asyncio.run_coroutine_threadsafe(close_clients(), LOOP).result(timeout=20)
        except Exception:
            pass


def main():
    global LOOP, HTTP_SERVER, SERVER_PORT
    LOG_FILE.write_text('', encoding='utf-8')
    PORT_FILE.unlink(missing_ok=True)
    log('[BOOT] Telegram Poster backend iniciando...')
    log(f'[BOOT] Python: {os.sys.version.split()[0]}')
    log(f'[BOOT] Pasta: {ROOT}')
    require_config()
    db().close()

    LOOP = asyncio.new_event_loop()
    asyncio.set_event_loop(LOOP)
    LOOP.create_task(scheduler_loop())
    LOOP.create_task(restore_accounts())

    SERVER_PORT = pick_port()
    HTTP_SERVER = ThreadingHTTPServer((HOST, SERVER_PORT), Handler)
    HTTP_SERVER.daemon_threads = True

    thread = threading.Thread(target=HTTP_SERVER.serve_forever, name='http-server', daemon=True)
    thread.start()
    PORT_FILE.write_text(str(SERVER_PORT), encoding='ascii')

    log(f'[READY] Backend ouvindo em http://{HOST}:{SERVER_PORT}')
    log('[READY] Health: /api/health')

    try:
        LOOP.run_forever()
    except KeyboardInterrupt:
        pass
    finally:
        shutdown()
        try:
            LOOP.stop()
            LOOP.close()
        except Exception:
            pass
        PORT_FILE.unlink(missing_ok=True)
        log('[EXIT] Backend finalizado.')


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        log('[FATAL]', repr(exc))
        traceback.print_exc()
        try:
            PORT_FILE.unlink(missing_ok=True)
        except Exception:
            pass
        raise
