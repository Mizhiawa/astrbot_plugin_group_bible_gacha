"""桩测试：在不安装 AstrBot 的环境下验证插件核心逻辑。

模拟 astrbot.api 各模块后导入 main.py，跑消息段解析、CQ 码解析、
编号解析、条目增删移转、渲染等纯逻辑，并对异步流程做冒烟测试。
"""

import asyncio
import json
import sys
import types
from pathlib import Path

PLUGIN_DIR = Path(__file__).parent
sys.path.insert(0, str(PLUGIN_DIR))
TMP_DIR = Path(__file__).parent / "_test_data"


# ---------------------------------------------------------------- astrbot 桩
def _make_stub_module(name: str, **attrs):
    mod = types.ModuleType(name)
    for k, v in attrs.items():
        setattr(mod, k, v)
    sys.modules[name] = mod
    return mod


class _Comp:
    def __init__(self, **kw):
        for k, v in kw.items():
            setattr(self, k, v)

    def __repr__(self):
        return f"<{type(self).__name__} {getattr(self, 'text', getattr(self, 'qq', getattr(self, 'id', '')))!r}>"


class Plain(_Comp):
    def __init__(self, text=""):
        super().__init__(text=text)


class Image(_Comp):
    def __init__(self, file="", **kw):
        super().__init__(file=file, **kw)

    @staticmethod
    def fromURL(url, **_):
        if not url.startswith(("http://", "https://")):
            raise Exception("not a valid url")
        return Image(file=url)

    @staticmethod
    def fromFileSystem(path, **_):
        return Image(file="file://" + str(path))

    @staticmethod
    def fromBase64(b64, **_):
        return Image(file="base64://" + b64)

    async def convert_to_file_path(self):
        p = TMP_DIR / "fake_dl.jpg"
        p.write_bytes(b"\xff\xd8fakejpeg")
        return str(p)


class At(_Comp):
    def __init__(self, **kw):
        super().__init__(**kw)


class AtAll(_Comp):
    pass


class Face(_Comp):
    def __init__(self, **kw):
        super().__init__(**kw)


class Reply(_Comp):
    pass


class Star:
    def __init__(self, context):
        self.context = context


class Context:
    pass


class StarTools:
    @staticmethod
    def get_data_dir(name=None):
        d = TMP_DIR / "plugin_data"
        d.mkdir(parents=True, exist_ok=True)
        return str(d)


logger = types.SimpleNamespace(
    info=lambda *a, **k: print("[info]", *a),
    warning=lambda *a, **k: print("[warn]", *a),
    error=lambda *a, **k: print("[error]", *a),
    debug=lambda *a, **k: None,
)


class _FilterNS:
    """模拟 astrbot.api.event.filter：装饰器原样返回函数。"""

    EventMessageType = types.SimpleNamespace(ALL="ALL", GROUP_MESSAGE="G", PRIVATE_MESSAGE="P", OTHER_MESSAGE="O")
    PlatformAdapterType = types.SimpleNamespace(AIOCQHTTP="aiocqhttp")
    PermissionType = types.SimpleNamespace(ADMIN="admin")

    @staticmethod
    def command(name, alias=None, **kw):
        def deco(fn):
            return fn
        return deco

    @staticmethod
    def event_message_type(t, priority=0):
        def deco(fn):
            return fn
        return deco

    @staticmethod
    def platform_adapter_type(t):
        def deco(fn):
            return fn
        return deco

    @staticmethod
    def permission_type(t):
        def deco(fn):
            return fn
        return deco


_make_stub_module(
    "astrbot",
    __path__=[],
)
_make_stub_module("astrbot.api", logger=logger)
_make_stub_module("astrbot.api.event", AstrMessageEvent=object, filter=_FilterNS, MessageChain=list)
_make_stub_module("astrbot.api.message_components", Plain=Plain, Image=Image, At=At, AtAll=AtAll, Face=Face, Reply=Reply)
_make_stub_module("astrbot.api.star", Context=Context, Star=Star, StarTools=StarTools)

import main  # noqa: E402


class FakeEvent:
    """最小可用的 event 桩。"""

    def __init__(self, raw=None, sender_id="10086", sender_name="测试群友", group_id="12345"):
        self.message_obj = types.SimpleNamespace(raw_message=raw or {}, message=[])
        self._sender_id = sender_id
        self._sender_name = sender_name
        self._group_id = group_id
        self.role = ""

    def get_group_id(self):
        return self._group_id

    def get_sender_id(self):
        return self._sender_id

    def get_sender_name(self):
        return self._sender_name

    def get_self_id(self):
        return "88888"

    def get_messages(self):
        return self.message_obj.message

    def get_message_str(self):
        return getattr(self, "_msg_str", "")

    def is_admin(self):
        return self.role == "admin"

    def plain_result(self, text):
        return ("plain", text)

    def chain_result(self, chain):
        return ("chain", chain)


def fresh_plugin():
    if TMP_DIR.exists():
        import shutil

        shutil.rmtree(TMP_DIR, ignore_errors=True)
    TMP_DIR.mkdir(parents=True, exist_ok=True)
    return main.GroupBibleGachaPlugin(Context(), {})


def test_parse_ids():
    assert main.GroupBibleGachaPlugin._parse_ids("圣经通过 3 5 3") == [3, 5]
    assert main.GroupBibleGachaPlugin._parse_ids("圣经通过 全部") is None
    assert main.GroupBibleGachaPlugin._parse_ids("圣经通过 all") is None
    assert main.GroupBibleGachaPlugin._parse_ids("圣经通过") is False
    print("test_parse_ids OK")


def test_cq_string():
    plugin = fresh_plugin()
    comps = plugin._parse_cq_string(
        "看这个&#91;厉害&#93;[CQ:image,url=https://example.com/a.jpg][CQ:face,id=12]哈哈"
    )
    kinds = [type(c).__name__ for c in comps]
    assert kinds == ["Plain", "Image", "Face", "Plain"], kinds
    assert "[厉害]" in comps[0].text
    assert comps[1].file == "https://example.com/a.jpg"
    # 纯文本
    comps = plugin._parse_cq_string("一句话圣经")
    assert len(comps) == 1 and comps[0].text == "一句话圣经"
    print("test_cq_string OK")


def test_segments():
    plugin = fresh_plugin()
    segs = [
        {"type": "text", "data": {"text": "前文"}},
        {"type": "image", "data": {"url": "https://e.com/1.jpg"}},
        {"type": "image", "data": {"file": "ABC.image"}},  # 缺直链
        {"type": "at", "data": {"qq": "10001"}},
        {"type": "at", "data": {"qq": "all"}},
        {"type": "face", "data": {"id": "5"}},
        {"type": "forward", "data": {}},
    ]
    comps, missing = plugin._parse_segments(segs)
    assert missing is True
    kinds = [type(c).__name__ for c in comps]
    assert kinds == ["Plain", "Image", "Plain", "At", "AtAll", "Face", "Plain"], kinds
    assert comps[2].text == "[图片]"
    print("test_segments OK")


def test_entry_lifecycle():
    plugin = fresh_plugin()

    async def run():
        gid = "12345"
        pool = main.GroupBibleGachaPlugin._group_state(plugin._pool, gid)
        # 模拟三条投稿直接入池（key 用与投稿相同的生成方式）
        for i in range(3):
            pool["entries"].append(
                {"id": pool["next_id"], "text": f"圣经{i}", "images": [], "sender_id": "1", "sender_name": "s", "time": 0, "source": "submit", "key": plugin._entry_key("1", f"圣经{i}", 0)},
            )
            pool["next_id"] += 1
        # 查重键命中
        key = plugin._entry_key("1", "圣经0", 0)
        assert any(e.get("key") == key for e in pool["entries"])
        # 移除 #1、#3，剩 #2
        removed = plugin._remove_entries(plugin._pool, gid, [1, 3])
        assert removed == [1, 3]
        assert len(pool["entries"]) == 1 and pool["entries"][0]["id"] == 2
        # 渲染
        comps = plugin._pool_components(pool["entries"][0])
        assert any(isinstance(c, Plain) and c.text == "圣经1" for c in comps)
        # 容量淘汰：上限 10，塞 15 条后只剩最新 10 条
        plugin2 = main.GroupBibleGachaPlugin(Context(), {"max_pool_size": 10})
        state = main.GroupBibleGachaPlugin._group_state(plugin2._pool, gid)
        for i in range(15):
            state["entries"].append({"id": i + 1, "text": f"t{i}", "images": [], "sender_id": "1", "sender_name": "s", "time": 0, "source": "submit", "key": f"x{i}"})
        plugin2._trim_pool(state)
        assert len(state["entries"]) == 10 and state["entries"][0]["text"] == "t5"

    asyncio.run(run())
    print("test_entry_lifecycle OK")


def test_render_draw():
    plugin = fresh_plugin()
    chain = plugin._render_draw(
        "essence",
        [Plain("一条圣经")],
        {"sender_id": "1", "sender_name": "张三", "operator_name": "李四", "time": 1761283200, "id": 99},
    )
    texts = [c.text for c in chain if isinstance(c, Plain)]
    joined = "".join(texts)
    assert "精华加冕" not in joined and "投稿圣典" not in joined  # 标题已去除
    assert "一条圣经" in joined
    assert "张三" in joined and "李四" in joined
    chain = plugin._render_draw("pool", [Plain("x")], {"sender_id": "1", "sender_name": "王五", "operator_name": "", "time": 0, "id": 7})
    texts = [c.text for c in chain if isinstance(c, Plain)]
    assert not any("#7" in t for t in texts)  # 抽卡展示不带编号
    print("test_render_draw OK")


def test_storage_roundtrip():
    plugin = fresh_plugin()
    gid = "777"

    async def run():
        state = main.GroupBibleGachaPlugin._group_state(plugin._pool, gid)
        state["entries"].append({"id": state["next_id"], "text": "存盘测试", "images": [], "sender_id": "1", "sender_name": "s", "time": 0, "source": "submit", "key": "kk"})
        state["next_id"] += 1
        await plugin._save(plugin._pool_file, plugin._pool)
        plugin2 = main.GroupBibleGachaPlugin(Context(), {})
        assert plugin2._group_state(plugin2._pool, gid)["entries"][0]["text"] == "存盘测试"

    asyncio.run(run())
    print("test_storage_roundtrip OK")


def test_poke_gate():
    raw_group_poke = {"post_type": "notice", "notice_type": "notify", "sub_type": "poke", "group_id": 12345, "user_id": 10086, "target_id": 88888}
    raw_other_poke = dict(raw_group_poke, target_id=10086)
    raw_recall = {"post_type": "notice", "notice_type": "group_recall", "group_id": 12345}
    assert main._raw_get(raw_group_poke, "sub_type") == "poke"
    assert main._raw_get(raw_other_poke, "target_id") == 10086
    assert main._raw_get(raw_recall, "notice_type") == "group_recall"
    print("test_poke_gate OK")


def test_import_dedup():
    plugin = fresh_plugin()
    gid = "555"
    state = main.GroupBibleGachaPlugin._group_state(plugin._pool, gid)
    key = plugin._entry_key("10086", "重复的圣经", 0)
    state["entries"].append({"id": 1, "text": "重复的圣经", "images": [], "sender_id": "10086", "sender_name": "s", "time": 0, "source": "essence", "key": key, "msg_id": 9001})
    state["next_id"] = 2
    assert key in {e.get("key") for e in state["entries"]}
    assert 9001 in {e.get("msg_id") for e in state["entries"]}
    print("test_import_dedup OK")


if __name__ == "__main__":
    test_parse_ids()
    test_cq_string()
    test_segments()
    test_entry_lifecycle()
    test_render_draw()
    test_storage_roundtrip()
    test_poke_gate()
    test_import_dedup()
    print("\nALL TESTS PASSED")
