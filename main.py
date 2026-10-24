"""群圣经 · 抽卡插件。

「/抽卡」从群精华消息与圣经池（群友投稿）中随机抽取一条发送展现；
群友可通过「/投稿」把文字或图片投进圣经池，管理员审核后入库；
被戳一戳时随机回敬一条圣经。支持分群开关管理与 SU（AstrBot 管理员）
审核、导入、重置等管理指令。

仅依赖 AstrBot 自带能力（OneBot v11 / aiocqhttp + NapCat），无第三方依赖。
"""

from __future__ import annotations

import asyncio
import base64
import hashlib
import json
import os
import random
import re
import shutil
import time
import traceback
from pathlib import Path
from urllib.parse import unquote, urlparse
from urllib.request import url2pathname
from uuid import uuid4

from astrbot.api import logger
from astrbot.api.event import AstrMessageEvent, filter
from astrbot.api.message_components import At, AtAll, Face, Image, Plain, Reply
from astrbot.api.star import Context, Star, StarTools

# 戳一戳监听器的优先级。AstrBot 中该值越大越先执行（默认 0），
# 静默监听类插件可能会拦截事件，取一个足够大的值保证能收到戳一戳。
POKE_LISTENER_PRIORITY = 99999
# 单张图片下载超时（秒）
IMAGE_TIMEOUT = 20
# 单张图片体积上限的兜底值（MB）
IMAGE_MAX_MB_DEFAULT = 10
# 单次投稿图片数量上限的兜底值
MAX_IMAGES_PER_SUBMIT_DEFAULT = 3
# 投稿正文长度上限
MAX_TEXT_LEN = 4000
# 抽卡展示时正文超长截断
DRAW_TEXT_LIMIT = 2500
# 列表预览的截断长度
PREVIEW_LEN = 60
# 审核列表一次最多展示条数
REVIEW_LIST_LIMIT = 20
# 冷却记录膨胀后的清理阈值
COOLDOWN_GC_SIZE = 4096
# 一次导入精华的条数上限
IMPORT_LIMIT = 1000
# 每群配置项的默认值
GROUP_DEFAULTS = {"gacha": True, "submit": True, "poke": True}
# 开关指令里的功能名 -> 配置键
SWITCH_KEYS = {
    "抽卡": "gacha",
    "gacha": "gacha",
    "投稿": "submit",
    "投稿池": "submit",
    "submit": "submit",
    "戳一戳": "poke",
    "poke": "poke",
}
# 开 / 关 的写法
SWITCH_ON = {"开", "on", "开启", "启用", "1", "true"}
SWITCH_OFF = {"关", "off", "关闭", "禁用", "0", "false"}


def _raw_get(raw, key: str, default=None):
    """从 OneBot 原始事件里取值，兼容 aiocqhttp 的 Event(dict) 与普通 dict。"""
    if raw is None:
        return default
    if isinstance(raw, dict):
        value = raw.get(key, default)
        return default if value is None else value
    value = getattr(raw, key, None)
    return default if value is None else value


def _local_path_from_ref(ref: str) -> str | None:
    """把图片引用解析成本地路径；http(s)/base64 返回 None。"""
    if not ref or ref.startswith(("http://", "https://", "base64://")):
        return None
    if ref.startswith("file://"):
        try:
            return url2pathname(unquote(urlparse(ref).path))
        except (ValueError, OSError):
            return None
    return ref


def _cq_unescape(text: str) -> str:
    """还原 CQ 码转义字符。"""
    for esc, ch in (("&amp;", "&"), ("&#91;", "["), ("&#93;", "]"), ("&#44;", ",")):
        text = text.replace(esc, ch)
    return text


CQ_CODE_RE = re.compile(r"\[CQ:([a-zA-Z0-9_.\-]+)((?:,[^\[\],]*=[^\[\]]*)*)\]")


class GroupBibleGachaPlugin(Star):
    """群圣经 · 抽卡

    - /抽卡：从群精华消息 / 圣经池随机抽一条发送
    - /投稿：把文字或图片投进本群圣经池（管理员审核后入库）
    - 戳一戳机器人：随机回敬一条圣经
    - /圣经帮助：查看全部指令
    """

    def __init__(self, context: Context, config: dict | None = None):
        super().__init__(context)
        self.config = config or {}
        try:
            self._data_dir = Path(StarTools.get_data_dir())
        except Exception as e:  # noqa: BLE001
            logger.warning(f"[群圣经] 数据目录创建失败，尝试退回默认路径：{e}")
            self._data_dir = Path("data/plugin_data/astrbot_plugin_group_bible_gacha")
        self._images_dir = self._data_dir / "images"
        try:
            self._images_dir.mkdir(parents=True, exist_ok=True)
        except OSError as e:
            logger.warning(f"[群圣经] 图片目录创建失败：{e}")

        self._pool_file = self._data_dir / "pool.json"
        self._pending_file = self._data_dir / "pending.json"
        self._settings_file = self._data_dir / "settings.json"
        # {"groups": {群号: {"next_id": int, "entries": [entry...]}}}
        self._pool: dict = self._load_json(self._pool_file, {"groups": {}})
        # 待审核投稿，结构与 pool 相同
        self._pending: dict = self._load_json(self._pending_file, {"groups": {}})
        # {群号: {"gacha": bool, "submit": bool, "poke": bool}}
        self._settings: dict = self._load_json(self._settings_file, {})

        self._store_lock = asyncio.Lock()
        # 冷却记录：(群号, QQ) / 群号 -> 上次时间戳
        self._gacha_cd: dict = {}
        self._submit_cd: dict = {}
        self._poke_cd: dict = {}
        # 精华列表缓存：群号 -> (缓存时间, 列表)
        self._essence_cache: dict = {}

    async def initialize(self) -> None:
        logger.info("[群圣经] 插件已加载：/抽卡 抽圣经，/投稿 投稿圣经，被戳也会回敬一条~")

    async def terminate(self) -> None:
        logger.info("[群圣经] 插件已卸载，圣经池数据保留在磁盘上。")

    # ------------------------------------------------------------------ 配置

    def _cfg(self, key: str, default):
        value = self.config.get(key, default) if hasattr(self.config, "get") else default
        return default if value is None else value

    def _cfg_int(self, key: str, default: int, minimum: int = 0) -> int:
        try:
            return max(minimum, int(self._cfg(key, default)))
        except (TypeError, ValueError):
            return default

    def _cfg_bool(self, key: str, default: bool) -> bool:
        value = self._cfg(key, default)
        return bool(value)

    def _cfg_list(self, key: str, default: list) -> list:
        value = self._cfg(key, default)
        if isinstance(value, list):
            return [str(v) for v in value if str(v).strip()]
        return default

    # ------------------------------------------------------------- 数据读写

    @staticmethod
    def _load_json(path: Path, default):
        try:
            with open(path, encoding="utf-8") as f:
                return json.load(f)
        except FileNotFoundError:
            return default
        except Exception as e:  # noqa: BLE001
            logger.warning(f"[群圣经] 读取 {path.name} 失败，已重置为默认：{e}")
            return default

    @staticmethod
    def _dump_json_sync(path: Path, data) -> None:
        tmp = path.with_suffix(path.suffix + ".tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
        os.replace(tmp, path)

    async def _save(self, path: Path, data) -> None:
        async with self._store_lock:
            try:
                await asyncio.to_thread(self._dump_json_sync, path, data)
            except Exception as e:  # noqa: BLE001
                logger.warning(f"[群圣经] 写入 {path.name} 失败：{e}")

    @staticmethod
    def _group_state(store: dict, gid: str) -> dict:
        groups = store.setdefault("groups", {})
        state = groups.setdefault(gid, {})
        state.setdefault("next_id", 1)
        state.setdefault("entries", [])
        return state

    def _delete_images(self, names: list) -> None:
        for name in names or []:
            try:
                path = self._images_dir / str(name)
                if path.is_file():
                    path.unlink()
            except OSError as e:
                logger.warning(f"[群圣经] 删除图片失败 {name}：{e}")

    # ----------------------------------------------------------- 群与权限

    def _gid(self, event: AstrMessageEvent) -> str:
        """群号；私聊返回空字符串。"""
        gid = ""
        try:
            gid = str(event.get_group_id() or "")
        except Exception:  # noqa: BLE001
            gid = ""
        if not gid:
            raw = getattr(event.message_obj, "raw_message", None)
            gid = str(_raw_get(raw, "group_id") or "")
        return gid

    def _is_moderator(self, event: AstrMessageEvent) -> bool:
        """审核权限：AstrBot 管理员（SU）始终可用；群主/群管理员可按配置放开。"""
        if event.is_admin():
            return True
        if not self._cfg_bool("allow_group_admin", True):
            return False
        raw = getattr(event.message_obj, "raw_message", None)
        sender = _raw_get(raw, "sender")
        role = str(_raw_get(sender, "role", "") or "")
        return role in ("owner", "admin")

    def _setting(self, gid: str, key: str) -> bool:
        default = GROUP_DEFAULTS[key]
        value = self._settings.get(gid, {}).get(key, default)
        return bool(value)

    # ------------------------------------------------------------- 冷却控制

    def _cooldown_ok(self, store: dict, key, seconds: int) -> bool:
        now = time.time()
        if len(store) > COOLDOWN_GC_SIZE:
            for k in [k for k, ts in store.items() if now - ts > max(seconds, 3600)]:
                store.pop(k, None)
        last = store.get(key)
        if last is not None and now - last < seconds:
            return False
        store[key] = now
        return True

    # --------------------------------------------------------- OneBot 调用

    async def _call(self, event: AstrMessageEvent, action: str, params: dict):
        """调用 OneBot API，失败返回 None。"""
        bot = getattr(event, "bot", None)
        if bot is None:
            return None
        for name in ("call_action", "call_api"):
            fn = getattr(bot, name, None)
            if not callable(fn):
                continue
            try:
                return await asyncio.wait_for(fn(action, **params), timeout=15)
            except asyncio.TimeoutError:
                logger.warning(f"[群圣经] OneBot {action} 超时")
                return None
            except TypeError:
                continue
            except Exception as e:  # noqa: BLE001
                logger.warning(f"[群圣经] OneBot {action} 调用失败：{e}")
                return None
        return None

    async def _fetch_essence(self, event: AstrMessageEvent, gid: str, force: bool = False):
        """获取群精华消息列表；失败返回 None，空群返回 []。带缓存。"""
        ttl = self._cfg_int("essence_cache_minutes", 10) * 60
        cached = self._essence_cache.get(gid)
        if cached and not force and ttl > 0 and time.time() - cached[0] < ttl:
            return cached[1]
        gid_param = int(gid) if gid.isdigit() else gid
        res = await self._call(event, "get_essence_msg_list", {"group_id": gid_param})
        items = None
        if isinstance(res, list):
            items = res
        elif isinstance(res, dict) and isinstance(res.get("data"), list):
            # 个别实现不自动拆 data 包裹
            items = res["data"]
        if items is None:
            return None
        self._essence_cache[gid] = (time.time(), items)
        return items

    # --------------------------------------------------------- 内容解析渲染

    def _parse_segments(self, segments: list) -> tuple[list, bool]:
        """OneBot 消息段数组 -> AstrBot 组件。返回 (组件列表, 是否有缺直链的图片)。"""
        comps: list = []
        missing_url = False
        for seg in segments or []:
            if not isinstance(seg, dict):
                continue
            seg_type = str(seg.get("type", ""))
            data = seg.get("data") or {}
            if seg_type == "text":
                text = str(data.get("text", ""))
                if text:
                    comps.append(Plain(text))
            elif seg_type == "image":
                comp = self._image_comp_from_ref(data.get("url") or data.get("file") or "")
                if comp is not None:
                    comps.append(comp)
                else:
                    missing_url = True
                    comps.append(Plain("[图片]"))
            elif seg_type == "face":
                try:
                    comps.append(Face(id=int(data.get("id", 0))))
                except (TypeError, ValueError):
                    comps.append(Plain("[表情]"))
            elif seg_type == "at":
                qq = str(data.get("qq", ""))
                if qq == "all":
                    comps.append(AtAll())
                elif qq:
                    comps.append(At(qq=qq))
            elif seg_type == "reply":
                continue  # 抽卡展示不还原引用链
            elif seg_type in ("forward", "node", "nodes"):
                comps.append(Plain("[合并转发消息]"))
            elif seg_type == "record":
                comps.append(Plain("[语音]"))
            elif seg_type == "video":
                comps.append(Plain("[视频]"))
            elif seg_type == "json":
                comps.append(Plain("[卡片消息]"))
            elif seg_type:
                comps.append(Plain(f"[{seg_type}]"))
        return comps, missing_url

    def _parse_cq_string(self, text: str) -> list:
        """CQ 码字符串 -> AstrBot 组件（部分实现返回字符串格式的 content）。"""
        comps: list = []
        pos = 0
        for m in CQ_CODE_RE.finditer(text):
            if m.start() > pos:
                plain = _cq_unescape(text[pos : m.start()])
                if plain.strip():
                    comps.append(Plain(plain))
            ctype = m.group(1)
            params: dict = {}
            for kv in (m.group(2) or "").lstrip(",").split(","):
                if "=" in kv:
                    k, _, v = kv.partition("=")
                    params[k.strip()] = _cq_unescape(v)
            if ctype == "image":
                comp = self._image_comp_from_ref(params.get("url") or params.get("file") or "")
                comps.append(comp if comp is not None else Plain("[图片]"))
            elif ctype == "face":
                try:
                    comps.append(Face(id=int(params.get("id", 0))))
                except (TypeError, ValueError):
                    comps.append(Plain("[表情]"))
            elif ctype == "at":
                qq = params.get("qq", "")
                comps.append(AtAll() if qq == "all" else At(qq=qq))
            elif ctype in ("forward", "node", "nodes"):
                comps.append(Plain("[合并转发消息]"))
            elif ctype not in ("reply", "text"):
                comps.append(Plain(f"[{ctype}]"))
            pos = m.end()
        if pos < len(text):
            tail = _cq_unescape(text[pos:])
            if tail.strip():
                comps.append(Plain(tail))
        return comps

    @staticmethod
    def _image_comp_from_ref(ref: str):
        """按引用构造 Image 组件；拿不到可用引用返回 None。"""
        ref = str(ref or "")
        if ref.startswith(("http://", "https://")):
            try:
                return Image.fromURL(ref)
            except Exception:  # noqa: BLE001
                return None
        if ref.startswith("base64://"):
            try:
                return Image.fromBase64(ref[len("base64://") :])
            except Exception:  # noqa: BLE001
                return None
        path = _local_path_from_ref(ref)
        if path and Path(path).is_file():
            try:
                return Image.fromFileSystem(path)
            except Exception:  # noqa: BLE001
                return None
        return None

    async def _essence_components(self, event: AstrMessageEvent, item: dict) -> list:
        """把一条精华消息渲染成组件；图片缺直链时用 get_msg 兜底。"""
        mid = item.get("message_id")
        content = item.get("content")
        comps: list = []
        if isinstance(content, list) and content:
            comps, missing = self._parse_segments(content)
            if not missing:
                return comps
        if mid is not None:
            res = await self._call(event, "get_msg", {"message_id": mid})
            msg = res.get("message") if isinstance(res, dict) else None
            if isinstance(msg, list) and msg:
                fresh, _ = self._parse_segments(msg)
                if fresh:
                    return fresh
            elif isinstance(msg, str) and msg:
                fresh = self._parse_cq_string(msg)
                if fresh:
                    return fresh
        if isinstance(content, str) and content:
            fresh = self._parse_cq_string(content)
            if fresh:
                return fresh
        return comps

    def _pool_components(self, entry: dict) -> list:
        """把圣经池条目渲染成组件。"""
        comps: list = []
        text = str(entry.get("text") or "")
        if text:
            comps.append(Plain(text if len(text) <= DRAW_TEXT_LIMIT else text[:DRAW_TEXT_LIMIT] + "……"))
        for name in entry.get("images") or []:
            path = self._images_dir / str(name)
            if path.is_file():
                try:
                    comps.append(Image.fromFileSystem(str(path)))
                except Exception:  # noqa: BLE001
                    comps.append(Plain("[图片加载失败]"))
            else:
                comps.append(Plain("[图片已丢失]"))
        return comps or [Plain("[空条目]")]

    @staticmethod
    def _essence_meta(item: dict) -> dict:
        sender_id = str(item.get("sender_id") or item.get("author_id") or "")
        sender_name = (
            item.get("sender_nick")
            or item.get("author_nick")
            or sender_id
            or "佚名"
        )
        operator = item.get("operator_nick") or (
            str(item.get("operator_id")) if item.get("operator_id") else ""
        )
        ts = item.get("time") or item.get("sender_time") or item.get("operator_time") or 0
        try:
            ts = int(ts)
        except (TypeError, ValueError):
            ts = 0
        return {
            "sender_id": sender_id,
            "sender_name": str(sender_name),
            "operator_name": str(operator),
            "time": ts,
            "id": item.get("message_id"),
        }

    @staticmethod
    def _pool_meta(entry: dict) -> dict:
        return {
            "sender_id": str(entry.get("sender_id") or ""),
            "sender_name": str(entry.get("sender_name") or ""),
            "operator_name": "",
            "time": int(entry.get("time") or 0),
            "id": entry.get("id"),
        }

    # ------------------------------------------------------------- 抽卡核心

    async def _draw(
        self,
        event: AstrMessageEvent,
        gid: str,
        source: str,
    ) -> tuple[str | None, list, dict | None]:
        """按来源抽一条。返回 (实际来源, 组件, 元信息)；抽不到返回 (None, [], None)。"""
        want_essence = source in ("essence", "both")
        want_pool = source in ("pool", "both")
        pool_entries = self._group_state(self._pool, gid)["entries"]

        essence_items = None
        if want_essence:
            essence_items = await self._fetch_essence(event, gid)
            if not essence_items:
                essence_items = None

        has_essence = bool(essence_items)
        has_pool = bool(pool_entries)
        if not (has_essence or has_pool):
            return None, [], None

        if want_essence and not want_pool:
            order = ["essence"]
        elif want_pool and not want_essence:
            order = ["pool"]
        else:
            order = ["essence", "pool"] if random.random() < 0.5 else ["pool", "essence"]

        for src in order:
            if src == "essence" and has_essence:
                item = random.choice(essence_items)
                comps = await self._essence_components(event, item)
                if comps:
                    return "essence", comps, self._essence_meta(item)
            elif src == "pool" and has_pool:
                entry = random.choice(pool_entries)
                return "pool", self._pool_components(entry), self._pool_meta(entry)
        return None, [], None

    def _render_draw(self, used_source: str, comps: list, meta: dict | None) -> list:
        chain: list = list(comps)
        info = "\n─────────────\n"
        if meta:
            who = meta.get("sender_name") or meta.get("sender_id") or "佚名"
            info += f"📖 出自：{who}"
            if used_source == "essence" and meta.get("operator_name"):
                info += f"　✍️ 加精：{meta['operator_name']}"
            if meta.get("time"):
                info += f"\n🕒 {time.strftime('%Y-%m-%d %H:%M', time.localtime(meta['time']))}"
            if used_source == "pool" and meta.get("id") is not None:
                info += f"\n📌 圣经池编号 #{meta['id']}"
        chain.append(Plain(info))
        return chain

    # ------------------------------------------------------------- 图片落盘

    async def _materialize_image(self, comp: Image) -> str | None:
        """把 Image 组件保存进插件图片目录，返回文件名；失败返回 None。

        注意 Image 组件的引用可能落在 url / file / path 任意一个字段上
        （Image.fromURL 只写 file），依次取第一个可用的。
        """
        url = str(getattr(comp, "url", "") or "")
        file_ref = str(getattr(comp, "file", "") or "")
        path_ref = str(getattr(comp, "path", "") or "")
        limit = self._cfg_int("image_max_mb", IMAGE_MAX_MB_DEFAULT, minimum=1) * 1024 * 1024
        src: Path | None = None
        tmp_path: Path | None = None

        try:
            http_ref = url if url.startswith(("http://", "https://")) else (
                file_ref if file_ref.startswith(("http://", "https://")) else ""
            )
            if http_ref:
                tmp_path = Path(
                    await asyncio.wait_for(
                        Image.fromURL(http_ref).convert_to_file_path(),
                        timeout=IMAGE_TIMEOUT,
                    ),
                )
                src = tmp_path if tmp_path.is_file() else None
            elif file_ref.startswith("base64://"):
                raw = base64.b64decode(file_ref[len("base64://") :])
                if len(raw) > limit:
                    return None
                tmp_path = self._images_dir / f"_tmp_{uuid4().hex}"
                tmp_path.write_bytes(raw)
                src = tmp_path
            else:
                local = _local_path_from_ref(path_ref or file_ref)
                if local and Path(local).is_file():
                    src = Path(local)
            if src is None:
                return None
            if src.stat().st_size > limit:
                return None

            suffix = src.suffix or ".jpg"
            name = f"{int(time.time() * 1000)}_{uuid4().hex[:8]}{suffix}"
            target = self._images_dir / name
            if src == target:
                return name
            try:
                await asyncio.to_thread(shutil.copy2, str(src), str(target))
            except Exception:  # noqa: BLE001
                logger.warning(f"[群圣经] 保存图片失败：{name}")
                return None
            return name
        except asyncio.TimeoutError:
            logger.warning("[群圣经] 图片下载超时，已跳过")
            return None
        except Exception as e:  # noqa: BLE001
            logger.warning(f"[群圣经] 图片处理失败：{e}")
            return None
        finally:
            if tmp_path is not None and tmp_path.name.startswith("_tmp_"):
                try:
                    tmp_path.unlink(missing_ok=True)
                except OSError:
                    pass

    @staticmethod
    def _entry_key(sender_id: str, text: str, image_count: int) -> str:
        raw = f"{sender_id}|{text.strip()}|{image_count}"
        return hashlib.sha1(raw.encode("utf-8")).hexdigest()

    # ============================================================== 用户指令

    @filter.command("抽卡", alias={"抽圣经", "圣经抽卡"})
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def gacha(self, event: AstrMessageEvent):
        """从群精华消息 / 圣经池随机抽取一条圣经"""
        gid = self._gid(event)
        if not gid:
            yield event.plain_result("圣经抽卡请在群聊中使用~")
            return
        if not self._setting(gid, "gacha"):
            yield event.plain_result("本群已关闭圣经抽卡（管理员可用 /圣经开关 抽卡 开 启用）")
            return

        arg = re.sub(r"^(?:抽圣经|圣经抽卡|抽卡)\s*", "", event.get_message_str().strip())
        if "精华" in arg:
            source = "essence"
        elif "池" in arg:
            source = "pool"
        else:
            source = str(self._cfg("gacha_source", "both"))

        if not self._cooldown_ok(
            self._gacha_cd,
            (gid, event.get_sender_id()),
            self._cfg_int("gacha_cooldown", 15),
        ):
            yield event.plain_result(
                f"手气太旺啦，歇 {self._cfg_int('gacha_cooldown', 15)} 秒再来抽~"
            )
            return

        try:
            used, comps, meta = await self._draw(event, gid, source)
        except Exception as e:  # noqa: BLE001
            logger.error(f"[群圣经] 抽卡失败：{traceback.format_exc() if self._cfg_bool('debug', False) else e}")
            used, comps, meta = None, [], None
        if used is None:
            hint = "没抽到东西：群精华暂时拿不到或为空，圣经池也是空的。\n快用 /投稿 投喂一点圣经吧！"
            if source == "essence":
                hint = "没抽到：获取群精华失败或群精华还是空的。"
            elif source == "pool":
                hint = "没抽到：圣经池还是空的，快用 /投稿 投喂第一条圣经吧！"
            yield event.plain_result(hint)
            return
        yield event.chain_result(self._render_draw(used, comps, meta))

    @filter.command("投稿", alias={"圣经投稿"})
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def submit(self, event: AstrMessageEvent):
        """投稿圣经：直接附文字/图片，或回复一条消息发 /投稿"""
        gid = self._gid(event)
        if not gid:
            yield event.plain_result("圣经投稿请在群聊中使用~")
            return
        if not self._setting(gid, "submit"):
            yield event.plain_result("本群已关闭圣经投稿（管理员可用 /圣经开关 投稿 开 启用）")
            return

        comps = event.get_messages()
        reply = next((c for c in comps if isinstance(c, Reply)), None)
        own_text = re.sub(
            r"^(?:圣经投稿|投稿)(?:\s+|(?=\S))?",
            "",
            event.get_message_str().strip(),
            count=1,
        ).strip()
        own_images = [c for c in comps if isinstance(c, Image)]

        text = ""
        image_comps: list[Image] = []
        if reply is not None:
            text = str(getattr(reply, "message_str", "") or getattr(reply, "text", "") or "").strip()
            for c in (reply.chain or []):
                if isinstance(c, Image):
                    image_comps.append(c)
            # 引用的消息没有内容时，退回用自己附带的文字/图片
            if not text and not image_comps:
                text, image_comps = own_text, own_images
        else:
            text, image_comps = own_text, own_images

        if not text and not image_comps:
            yield event.plain_result(
                "投稿姿势不对哦：\n"
                "1. 直接发「/投稿 要投稿的文字」（可带图片）\n"
                "2. 回复一条消息发「/投稿」，把该消息收进圣经池"
            )
            return
        if len(text) > MAX_TEXT_LEN:
            yield event.plain_result(f"投稿文字太长啦（上限 {MAX_TEXT_LEN} 字），精简一点再投~")
            return

        max_images = self._cfg_int("max_images_per_submit", MAX_IMAGES_PER_SUBMIT_DEFAULT, minimum=1)
        if len(image_comps) > max_images:
            yield event.plain_result(f"一次最多投稿 {max_images} 张图片，少一点再投~")
            return
        if not self._cooldown_ok(
            self._submit_cd,
            (gid, event.get_sender_id()),
            self._cfg_int("submit_cooldown", 60),
        ):
            yield event.plain_result(
                f"投稿太勤啦，歇 {self._cfg_int('submit_cooldown', 60)} 秒再来~"
            )
            return

        saved: list[str] = []
        for comp in image_comps:
            name = await self._materialize_image(comp)
            if name:
                saved.append(name)
        if image_comps and not saved:
            yield event.plain_result("图片保存失败了，稍后再试试吧~")
            return
        if not text and not saved:
            yield event.plain_result("这条内容没有可投稿的文字或图片。")
            return

        entry = {
            "id": 0,
            "text": text,
            "images": saved,
            "sender_id": event.get_sender_id(),
            "sender_name": event.get_sender_name() or event.get_sender_id(),
            "time": int(time.time()),
            "source": "submit",
            "key": self._entry_key(event.get_sender_id(), text, len(saved)),
        }
        async with self._store_lock:
            state = self._group_state(self._pending, gid)
            entry["id"] = state["next_id"]
            state["next_id"] += 1
            state["entries"].append(entry)
            await asyncio.to_thread(self._dump_json_sync, self._pending_file, self._pending)

        yield event.plain_result(
            f"✅ 投稿成功！圣经编号 #{entry['id']}，等待管理员 /圣经审核 后入库~"
        )

    @filter.command("圣经池")
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def pool_info(self, event: AstrMessageEvent):
        """查看本群圣经池概况"""
        gid = self._gid(event)
        if not gid:
            yield event.plain_result("请在群聊中查看圣经池~")
            return
        state = self._group_state(self._pool, gid)
        pending_state = self._group_state(self._pending, gid)
        entries = state["entries"]
        lines = [
            f"📚 本群圣经池共 {len(entries)} 条（待审核 {len(pending_state['entries'])} 条）",
        ]
        if entries:
            lines.append("最近入库的几条：")
            for entry in entries[-5:]:
                preview = entry.get("text", "").strip()[:PREVIEW_LEN]
                if not preview:
                    marks = []
                    if entry.get("images"):
                        marks.append(f"图片x{len(entry['images'])}")
                    preview = " ".join(marks) or "[空]"
                lines.append(f"#{entry['id']} {preview}")
            lines.append("抽一条看看：/抽卡 池")
        else:
            lines.append("还是空的，快用 /投稿 开光！")
        yield event.plain_result("\n".join(lines))

    @filter.command("圣经预览")
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def preview_entry(self, event: AstrMessageEvent):
        """预览某条投稿/圣经（圣经预览 编号）"""
        gid = self._gid(event)
        match = re.search(r"\d+", re.sub(r"^圣经预览\s*", "", event.get_message_str().strip()))
        if not gid or not match:
            yield event.plain_result("用法：/圣经预览 编号（可预览待审核或已入库的圣经）")
            return
        entry = self._find_entry(self._pending, gid, int(match.group()))
        where = "待审核投稿"
        if entry is None:
            entry = self._find_entry(self._pool, gid, int(match.group()))
            where = "圣经池"
        if entry is None:
            yield event.plain_result(f"没找到编号 #{match.group()} 的条目。")
            return
        chain = [Plain(f"🔍 {where} #{entry['id']}（投稿人：{entry.get('sender_name', '')}）：\n")]
        chain.extend(self._pool_components(entry))
        yield event.chain_result(chain)

    # ================================================================ 管理指令

    @filter.command("圣经审核")
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def review_list(self, event: AstrMessageEvent):
        """列出本群待审核投稿（群管理员/AstrBot 管理员）"""
        gid = self._gid(event)
        if not gid:
            yield event.plain_result("请在群聊中使用审核指令~")
            return
        if not self._is_moderator(event):
            yield event.plain_result("该指令需要群管理员或 AstrBot 管理员权限。")
            return
        entries = self._group_state(self._pending, gid)["entries"]
        if not entries:
            yield event.plain_result("本群暂无待审核投稿。")
            return
        lines = [f"📋 待审核投稿共 {len(entries)} 条："]
        for entry in entries[:REVIEW_LIST_LIMIT]:
            preview = entry.get("text", "").strip()[:PREVIEW_LEN]
            if not preview:
                marks = []
                if entry.get("images"):
                    marks.append(f"图片x{len(entry['images'])}")
                preview = " ".join(marks) or "[空]"
            lines.append(f"#{entry['id']} {preview} —— {entry.get('sender_name', '')}")
        if len(entries) > REVIEW_LIST_LIMIT:
            lines.append(f"……其余 {len(entries) - REVIEW_LIST_LIMIT} 条略")
        lines.append("通过：/圣经通过 编号（多个空格隔开，或「全部」）")
        yield event.plain_result("\n".join(lines))

    @filter.command("圣经通过")
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def approve(self, event: AstrMessageEvent):
        """通过投稿：/圣经通过 编号... 或 /圣经通过 全部"""
        gid = self._gid(event)
        if not gid:
            yield event.plain_result("请在群聊中使用审核指令~")
            return
        if not self._is_moderator(event):
            yield event.plain_result("该指令需要群管理员或 AstrBot 管理员权限。")
            return
        ids = self._parse_ids(event.get_message_str())
        if ids is False:
            yield event.plain_result("用法：/圣经通过 编号（多个空格隔开，或「全部」）")
            return
        async with self._store_lock:
            moved = self._move_entries(self._pending, self._pool, gid, ids)
            await asyncio.to_thread(self._dump_json_sync, self._pending_file, self._pending)
            await asyncio.to_thread(self._dump_json_sync, self._pool_file, self._pool)
        if moved:
            detail = "、".join(f"#{old}→#{new}" for old, new in moved)
            yield event.plain_result(
                f"✅ 已通过 {detail}，收入圣经池！"
                f"当前池共 {len(self._group_state(self._pool, gid)['entries'])} 条。"
            )
        else:
            yield event.plain_result("没有匹配的待审核投稿。")

    @filter.command("圣经拒绝")
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def reject(self, event: AstrMessageEvent):
        """拒绝投稿：/圣经拒绝 编号... 或 /圣经拒绝 全部"""
        gid = self._gid(event)
        if not gid:
            yield event.plain_result("请在群聊中使用审核指令~")
            return
        if not self._is_moderator(event):
            yield event.plain_result("该指令需要群管理员或 AstrBot 管理员权限。")
            return
        ids = self._parse_ids(event.get_message_str())
        if ids is False:
            yield event.plain_result("用法：/圣经拒绝 编号（多个空格隔开，或「全部」）")
            return
        async with self._store_lock:
            removed = self._remove_entries(self._pending, gid, ids)
            await asyncio.to_thread(self._dump_json_sync, self._pending_file, self._pending)
        if removed:
            ids_text = "全部" if ids is None else "、".join(f"#{i}" for i in removed)
            yield event.plain_result(f"🗑️ 已拒绝并清理 {ids_text}。")
        else:
            yield event.plain_result("没有匹配的待审核投稿。")

    @filter.command("圣经移除")
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def remove_from_pool(self, event: AstrMessageEvent):
        """从圣经池移除：/圣经移除 编号..."""
        gid = self._gid(event)
        if not gid:
            yield event.plain_result("请在群聊中使用管理指令~")
            return
        if not self._is_moderator(event):
            yield event.plain_result("该指令需要群管理员或 AstrBot 管理员权限。")
            return
        ids = self._parse_ids(event.get_message_str())
        if not ids:
            yield event.plain_result("用法：/圣经移除 编号（多个空格隔开，不支持「全部」）")
            return
        async with self._store_lock:
            removed = self._remove_entries(self._pool, gid, ids)
            await asyncio.to_thread(self._dump_json_sync, self._pool_file, self._pool)
        if removed:
            yield event.plain_result("、".join(f"#{i}" for i in removed) + " 已移出圣经池。")
        else:
            yield event.plain_result("没有匹配的圣经池条目。")

    @filter.command("圣经导入")
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def import_essence(self, event: AstrMessageEvent):
        """把本群精华消息导入圣经池（仅 AstrBot 管理员）"""
        gid = self._gid(event)
        if not gid:
            yield event.plain_result("请在群聊中使用管理指令~")
            return
        if not event.is_admin():
            yield event.plain_result("导入精华仅限 AstrBot 管理员（SU）使用。")
            return
        items = await self._fetch_essence(event, gid, force=True)
        if items is None:
            yield event.plain_result("获取群精华失败（可能机器人权限不足），稍后再试。")
            return
        if not items:
            yield event.plain_result("本群还没有精华消息。")
            return

        state = self._group_state(self._pool, gid)
        existing_keys = {entry.get("key") for entry in state["entries"]}
        existing_msg_ids = {entry.get("msg_id") for entry in state["entries"]}
        max_images = self._cfg_int("max_images_per_submit", MAX_IMAGES_PER_SUBMIT_DEFAULT, minimum=1)

        imported = skipped = 0
        for item in items[:IMPORT_LIMIT]:
            sender_id = str(item.get("sender_id") or item.get("author_id") or "")
            text = ""
            image_names: list[str] = []
            for seg in item.get("content") or []:
                if not isinstance(seg, dict):
                    continue
                if seg.get("type") == "text":
                    text += str((seg.get("data") or {}).get("text", ""))
                elif seg.get("type") == "image":
                    if len(image_names) >= max_images:
                        continue
                    ref = (seg.get("data") or {}).get("url") or (seg.get("data") or {}).get("file") or ""
                    comp = self._image_comp_from_ref(ref)
                    if comp is not None:
                        name = await self._materialize_image(comp)
                        if name:
                            image_names.append(name)
            key = self._entry_key(sender_id, text, len(image_names))
            msg_id = item.get("message_id")
            if key in existing_keys or msg_id in existing_msg_ids:
                skipped += 1
                # 已存在但此前没保存图片的旧条目不再补图，保持导入幂等
                continue
            if not text and not image_names:
                skipped += 1
                continue
            state["entries"].append(
                {
                    "id": state["next_id"],
                    "text": text[:MAX_TEXT_LEN],
                    "images": image_names,
                    "sender_id": sender_id,
                    "sender_name": str(
                        item.get("sender_nick")
                        or item.get("author_nick")
                        or sender_id
                        or "佚名"
                    ),
                    "time": int(item.get("time") or item.get("sender_time") or 0),
                    "source": "essence",
                    "key": key,
                    "msg_id": msg_id,
                },
            )
            state["next_id"] += 1
            existing_keys.add(key)
            existing_msg_ids.add(msg_id)
            imported += 1

        self._trim_pool(state)
        await asyncio.to_thread(self._dump_json_sync, self._pool_file, self._pool)
        yield event.plain_result(
            f"📖 导入完成：共 {len(items)} 条精华，新增 {imported} 条，跳过重复/空 {skipped} 条。"
            f"当前圣经池共 {len(state['entries'])} 条。"
        )

    @filter.command("圣经重置")
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def reset_pool(self, event: AstrMessageEvent):
        """清空本群圣经池与待审核（仅 AstrBot 管理员）：/圣经重置 确认"""
        gid = self._gid(event)
        if not gid:
            yield event.plain_result("请在群聊中使用管理指令~")
            return
        if not event.is_admin():
            yield event.plain_result("重置仅限 AstrBot 管理员（SU）使用。")
            return
        if "确认" not in event.get_message_str():
            state = self._group_state(self._pool, gid)
            pending_state = self._group_state(self._pending, gid)
            yield event.plain_result(
                f"⚠️ 将清空本群圣经池 {len(state['entries'])} 条与待审核 "
                f"{len(pending_state['entries'])} 条，且不可恢复。\n"
                f"确认请发：/圣经重置 确认",
            )
            return
        async with self._store_lock:
            for state in (
                self._group_state(self._pool, gid),
                self._group_state(self._pending, gid),
            ):
                for entry in state["entries"]:
                    self._delete_images(entry.get("images") or [])
                state["entries"] = []
                state["next_id"] = 1
            self._settings.pop(gid, None)
            await asyncio.to_thread(self._dump_json_sync, self._pool_file, self._pool)
            await asyncio.to_thread(self._dump_json_sync, self._pending_file, self._pending)
            await asyncio.to_thread(self._dump_json_sync, self._settings_file, self._settings)
        self._essence_cache.pop(gid, None)
        yield event.plain_result("🧹 本群圣经池、待审核与分群设置已全部清空。")

    @filter.command("圣经开关")
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def toggle(self, event: AstrMessageEvent):
        """分群开关：/圣经开关 抽卡|投稿|戳一戳 开|关"""
        gid = self._gid(event)
        if not gid:
            yield event.plain_result("请在群聊中使用管理指令~")
            return
        if not self._is_moderator(event):
            yield event.plain_result("该指令需要群管理员或 AstrBot 管理员权限。")
            return
        parts = re.sub(r"^(?:圣经开关)\s*", "", event.get_message_str().strip()).split()
        if len(parts) < 2 or parts[0] not in SWITCH_KEYS or (
            parts[1].lower() not in SWITCH_ON and parts[1].lower() not in SWITCH_OFF
        ):
            yield event.plain_result("用法：/圣经开关 抽卡|投稿|戳一戳 开|关")
            return
        key = SWITCH_KEYS[parts[0]]
        value = parts[1].lower() in SWITCH_ON
        group_settings = self._settings.setdefault(gid, {})
        group_settings[key] = value
        await asyncio.to_thread(self._dump_json_sync, self._settings_file, self._settings)
        name = {"gacha": "圣经抽卡", "submit": "圣经投稿", "poke": "戳一戳回复"}[key]
        yield event.plain_result(f"{'✅ 已开启' if value else '🚫 已关闭'}本群的{name}。")

    @filter.command("圣经状态")
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def status(self, event: AstrMessageEvent):
        """查看本群功能开关与池子状态"""
        gid = self._gid(event)
        if not gid:
            yield event.plain_result("请在群聊中查看状态~")
            return
        pool_state = self._group_state(self._pool, gid)
        pending_state = self._group_state(self._pending, gid)
        cached = self._essence_cache.get(gid)
        essence_text = f"已缓存 {len(cached[1])} 条" if cached else "未缓存（/抽卡 时自动获取）"
        lines = [
            "📊 本群圣经状态：",
            f"· 抽卡：{'开' if self._setting(gid, 'gacha') else '关'}　"
            f"投稿：{'开' if self._setting(gid, 'submit') else '关'}　"
            f"戳一戳：{'开' if self._setting(gid, 'poke') else '关'}",
            f"· 圣经池：{len(pool_state['entries'])} 条　待审核：{len(pending_state['entries'])} 条",
            f"· 群精华：{essence_text}",
        ]
        yield event.plain_result("\n".join(lines))

    @filter.command("圣经帮助")
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def help_cmd(self, event: AstrMessageEvent):
        """查看群圣经的全部指令"""
        text = (
            "📖 群圣经 · 指令一览\n"
            "─────────────\n"
            "🎴 /抽卡 —— 从群精华/圣经池随机抽一条（/抽卡 精华、/抽卡 池 可指定来源）\n"
            "🙏 /投稿 文字 —— 投稿圣经（可带图片）\n"
            "↩️ 回复一条消息发 /投稿 —— 把该消息投进圣经池\n"
            "📚 /圣经池 —— 查看本群圣经池概况\n"
            "🔍 /圣经预览 编号 —— 预览某条投稿/圣经\n"
            "─────────────\n"
            "🛡️ 管理员：\n"
            "/圣经审核 —— 列出待审核投稿\n"
            "/圣经通过 编号|全部 —— 收入圣经池\n"
            "/圣经拒绝 编号|全部 —— 退回投稿\n"
            "/圣经移除 编号 —— 移出圣经池\n"
            "/圣经开关 抽卡|投稿|戳一戳 开|关 —— 分群开关\n"
            "/圣经状态 —— 查看本群状态\n"
            "👑 SU（AstrBot 管理员）：\n"
            "/圣经导入 —— 把群精华导入圣经池\n"
            "/圣经重置 确认 —— 清空本群数据\n"
            "✨ 被戳一戳也会随机回敬一条圣经哦"
        )
        yield event.plain_result(text)

    # ============================================================ 戳一戳监听

    @filter.event_message_type(filter.EventMessageType.ALL, priority=POKE_LISTENER_PRIORITY)
    @filter.platform_adapter_type(filter.PlatformAdapterType.AIOCQHTTP)
    async def on_raw_event(self, event: AstrMessageEvent):
        """监听 OneBot notice 事件：群友戳机器人时随机回敬一条圣经。"""
        try:
            raw = getattr(event.message_obj, "raw_message", None)
            if _raw_get(raw, "post_type") != "notice":
                return
            if _raw_get(raw, "notice_type") != "notify" or _raw_get(raw, "sub_type") != "poke":
                return
            gid = str(_raw_get(raw, "group_id") or "")
            if not gid:
                return  # 好友戳一戳不参与群圣经
            if str(_raw_get(raw, "target_id") or "") != str(event.get_self_id()):
                return  # 只在被戳时回应，避免刷屏
            if not self._cfg_bool("poke_reply_enabled", True) or not self._setting(gid, "poke"):
                return
            if not self._cooldown_ok(self._poke_cd, gid, self._cfg_int("poke_cooldown", 30)):
                return

            poker = str(_raw_get(raw, "user_id") or event.get_sender_id())
            source = str(self._cfg("poke_reply_source", "both"))
            comps: list = []
            if source != "text":
                try:
                    _, comps, _ = await self._draw(event, gid, source)
                except Exception as e:  # noqa: BLE001
                    logger.warning(f"[群圣经] 戳一戳抽卡失败：{e}")
            if comps:
                chain: list = [
                    At(qq=poker),
                    Plain(" 你戳了戳我，于是给你抽了条群圣经：\n─────────────\n"),
                ]
                chain.extend(comps)
            else:
                texts = self._cfg_list("poke_texts", []) or [
                    "别戳啦，圣经在 /抽卡 里，自己去抽！",
                ]
                chain = [At(qq=poker), Plain(" " + random.choice(texts))]
            yield event.chain_result(chain)
        except Exception as e:  # noqa: BLE001
            # 监听器绝不向外抛异常，避免连累其他插件的事件处理
            logger.warning(f"[群圣经] 处理戳一戳事件失败：{e}")

    # ------------------------------------------------------------- 条目操作

    @staticmethod
    def _parse_ids(message_str: str):
        """从指令文本解析编号列表；含「全部/all」返回 None（表示全部）；解析不出返回 False。"""
        text = re.sub(r"^(?:圣经通过|圣经拒绝|圣经移除)\s*", "", message_str.strip())
        if re.search(r"全部|all", text, re.IGNORECASE):
            return None
        ids = sorted({int(x) for x in re.findall(r"\d+", text)})
        return ids if ids else False

    @staticmethod
    def _find_entry(store: dict, gid: str, entry_id: int) -> dict | None:
        for entry in store.get("groups", {}).get(gid, {}).get("entries", []):
            if entry.get("id") == entry_id:
                return entry
        return None

    def _move_entries(
        self,
        src_store: dict,
        dst_store: dict,
        gid: str,
        ids: list[int] | None,
    ) -> list[tuple[int, int]]:
        """待审核 -> 圣经池。ids 为 None 表示全部。返回 (投稿编号, 池编号) 列表。"""
        src_state = self._group_state(src_store, gid)
        dst_state = self._group_state(dst_store, gid)
        moved: list[tuple[int, int]] = []
        keep: list[dict] = []
        for entry in src_state["entries"]:
            if ids is None or entry.get("id") in ids:
                old_id = entry["id"]
                entry["id"] = dst_state["next_id"]
                dst_state["next_id"] += 1
                dst_state["entries"].append(entry)
                moved.append((old_id, entry["id"]))
            else:
                keep.append(entry)
        if moved:
            src_state["entries"] = keep
            self._trim_pool(dst_state)
        return moved

    def _remove_entries(self, store: dict, gid: str, ids: list[int] | None) -> list[int]:
        """从指定库删除条目并清理图片。ids 为 None 表示全部。返回删除的编号。"""
        state = self._group_state(store, gid)
        removed: list[int] = []
        keep: list[dict] = []
        for entry in state["entries"]:
            if ids is None or entry.get("id") in ids:
                self._delete_images(entry.get("images") or [])
                removed.append(entry.get("id"))
            else:
                keep.append(entry)
        state["entries"] = keep
        return removed

    def _trim_pool(self, state: dict) -> None:
        """圣经池超容量时从最旧的开始淘汰。"""
        max_size = self._cfg_int("max_pool_size", 500, minimum=10)
        entries = state["entries"]
        while len(entries) > max_size:
            entry = entries.pop(0)
            self._delete_images(entry.get("images") or [])
