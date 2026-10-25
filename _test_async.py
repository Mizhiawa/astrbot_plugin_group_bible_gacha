"""异步冒烟测试：用假 bot/event 走完 抽卡/投稿/审核/戳一戳 全链路。"""

import asyncio
import sys
import time
import types
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

import _test_stubs as stubs  # noqa: E402  复用桩与导入
from _test_stubs import (  # noqa: E402
    Context,
    FakeEvent,
    Image,
    Plain,
    Reply,
    TMP_DIR,
    fresh_plugin,
)


class FakeBot:
    """假 OneBot 客户端：call_action / call_api 双入口。"""

    def __init__(self, essence=None, msgs=None):
        self.essence = essence or []
        self.msgs = msgs or {}
        self.calls = []

    async def call_action(self, action, **params):
        return await self.call_api(action, **params)

    async def call_api(self, action, **params):
        self.calls.append((action, params))
        if action == "get_essence_msg_list":
            return list(self.essence)
        if action == "get_msg":
            return self.msgs.get(params.get("message_id"))
        return {}


def drain(gen):
    out = []
    for item in gen:
        out.append(item)
    return out


async def run_handler(agen):
    results = []
    async for res in agen:
        results.append(res)
    return results


async def test_gacha_from_essence():
    plugin = fresh_plugin()
    bot = FakeBot(
        essence=[
            {
                "sender_id": 10086,
                "sender_nick": "张三",
                "operator_id": 10010,
                "operator_nick": "群主",
                "time": 1761283200,
                "message_id": 9001,
                "content": [
                    {"type": "text", "data": {"text": "今天也是充满希望的一天呢"}},
                    {"type": "image", "data": {"url": "https://example.com/x.jpg"}},
                ],
            },
        ],
    )
    event = FakeEvent()
    event.bot = bot
    results = await run_handler(plugin.gacha(event))
    assert results, "抽卡应有输出"
    kind, chain = results[0]
    assert kind == "chain"
    texts = "".join(c.text for c in chain if isinstance(c, Plain))
    assert "精华加冕" not in texts  # 标题已去除
    assert "张三" in texts and "群主" in texts
    assert any(isinstance(c, Image) and c.file == "https://example.com/x.jpg" for c in chain)
    print("test_gacha_from_essence OK")


async def test_gacha_fallback_to_pool():
    plugin = fresh_plugin()
    bot = FakeBot(essence=[])  # 精华为空
    event = FakeEvent()
    event.bot = bot
    state = main.GroupBibleGachaPlugin._group_state(plugin._pool, "12345")
    state["entries"].append({"id": 1, "text": "池子圣经", "images": [], "sender_id": "2", "sender_name": "李四", "time": 0, "source": "submit", "key": "k"})
    state["next_id"] = 2
    results = await run_handler(plugin.gacha(event))
    kind, chain = results[0]
    texts = "".join(c.text for c in chain if isinstance(c, Plain))
    assert "投稿圣典" not in texts  # 标题已去除
    assert "池子圣经" in texts
    print("test_gacha_fallback_to_pool OK")


async def test_gacha_both_empty():
    plugin = fresh_plugin()
    bot = FakeBot(essence=[])
    event = FakeEvent()
    event.bot = bot
    results = await run_handler(plugin.gacha(event))
    assert results and results[0][0] == "plain"
    assert "投喂" in results[0][1] or "空" in results[0][1]
    print("test_gacha_both_empty OK")


async def test_gacha_get_msg_fallback_for_missing_url():
    plugin = fresh_plugin()
    # 精华返回的图片缺 url，但 get_msg 能拿到带 url 的完整消息
    bot = FakeBot(
        essence=[
            {"sender_id": 1, "sender_nick": "A", "message_id": 42, "time": 0,
             "content": [{"type": "text", "data": {"text": "看图"}}, {"type": "image", "data": {"file": "NOURL.image"}}]},
        ],
        msgs={
            42: {"message_id": 42, "message": [
                {"type": "text", "data": {"text": "看图"}},
                {"type": "image", "data": {"url": "https://cdn.example.com/fresh.jpg"}},
            ]},
        },
    )
    event = FakeEvent()
    event.bot = bot
    results = await run_handler(plugin.gacha(event))
    _, chain = results[0]
    assert any(isinstance(c, Image) and c.file == "https://cdn.example.com/fresh.jpg" for c in chain)
    print("test_gacha_get_msg_fallback_for_missing_url OK")


async def test_submit_direct_to_pool():
    import main

    plugin = fresh_plugin()
    event = FakeEvent()
    event._msg_str = "投稿 天下第一圣经"
    results = await run_handler(plugin.submit(event))
    assert "投稿成功" in results[0][1]
    pool = main.GroupBibleGachaPlugin._group_state(plugin._pool, "12345")
    assert pool["entries"][0]["text"] == "天下第一圣经"
    assert pool["entries"][0]["id"] == 1

    # 重复投稿被查重拒绝（清掉冷却再投一次）
    plugin._submit_cd.clear()
    event2 = FakeEvent()
    event2._msg_str = "投稿 天下第一圣经"
    results = await run_handler(plugin.submit(event2))
    assert "已经在池子里" in results[0][1]
    assert len(pool["entries"]) == 1

    # 审核指令已移除
    assert not hasattr(plugin, "review_list")
    assert not hasattr(plugin, "approve")
    assert not hasattr(plugin, "reject")

    # 群管理员移除
    admin = FakeEvent(raw={"sender": {"role": "admin"}})
    admin._msg_str = "圣经移除 1"
    results = await run_handler(plugin.remove_from_pool(admin))
    assert "已移出" in results[0][1]
    assert not main.GroupBibleGachaPlugin._group_state(plugin._pool, "12345")["entries"]
    print("test_submit_direct_to_pool OK")


async def test_whitelist():
    import main

    plugin = fresh_plugin()
    plugin.config = {"group_whitelist": ["999"]}
    bot = FakeBot(essence=[
        {"sender_id": 1, "sender_nick": "A", "message_id": 1, "time": 0,
         "content": [{"type": "text", "data": {"text": "白名单群圣经"}}]},
    ])
    # 非白名单群：抽卡静默无输出
    event = FakeEvent(group_id="12345")
    event.bot = bot
    assert not await run_handler(plugin.gacha(event))
    # 非白名单群：投稿也静默
    event = FakeEvent(group_id="12345")
    event.bot = bot
    event._msg_str = "投稿 测试"
    assert not await run_handler(plugin.submit(event))
    assert not main.GroupBibleGachaPlugin._group_state(plugin._pool, "12345")["entries"]
    # 白名单群：正常抽卡
    event = FakeEvent(group_id="999")
    event.bot = bot
    results = await run_handler(plugin.gacha(event))
    assert results and results[0][0] == "chain"
    # 非白名单群：戳一戳保持沉默
    raw = {"post_type": "notice", "notice_type": "notify", "sub_type": "poke",
           "group_id": 12345, "user_id": 10086, "target_id": 88888}
    e = FakeEvent(raw=raw)
    e.bot = bot
    assert not await run_handler(plugin.on_raw_event(e))
    # 白名单群：戳一戳正常回复
    raw999 = dict(raw, group_id=999)
    e = FakeEvent(raw=raw999)
    e.bot = bot
    assert await run_handler(plugin.on_raw_event(e))
    # 私聊不受白名单限制：投稿返回"请在群聊中使用"提示而非静默
    e = FakeEvent(group_id="")
    e.bot = bot
    e._msg_str = "投稿 私聊测试"
    results = await run_handler(plugin.submit(e))
    assert results and "群聊" in results[0][1]
    print("test_whitelist OK")


async def test_submit_via_reply_with_image():
    import main

    plugin = fresh_plugin()
    event = FakeEvent()
    event._msg_str = "投稿"
    quoted = Image(file="https://example.com/quoted.jpg")
    event.message_obj.message = [
        Reply(id="42", chain=[Plain("图配文"), quoted], message_str="图配文", sender_id="10010"),
    ]
    # 给 FakeBot 一个 get_msg（本用例直接用 Reply.chain，无需调用）
    event.bot = FakeBot()
    results = await run_handler(plugin.submit(event))
    assert "投稿成功" in results[0][1]
    entry = main.GroupBibleGachaPlugin._group_state(plugin._pool, "12345")["entries"][0]
    assert entry["text"] == "图配文"
    assert len(entry["images"]) == 1
    saved = TMP_DIR / "plugin_data" / "images" / entry["images"][0]
    assert saved.is_file(), "图片应已复制进插件图片目录"
    print("test_submit_via_reply_with_image OK")


async def test_poke_reply_and_cooldown():
    plugin = fresh_plugin()
    bot = FakeBot(essence=[
        {"sender_id": 1, "sender_nick": "A", "message_id": 1, "time": 0,
         "content": [{"type": "text", "data": {"text": "戳我抽到的圣经"}}]},
    ])
    raw = {"post_type": "notice", "notice_type": "notify", "sub_type": "poke",
           "group_id": 12345, "user_id": 10086, "target_id": 88888}
    event = FakeEvent(raw=raw)
    event.bot = bot
    results = await run_handler(plugin.on_raw_event(event))
    assert results, "被戳应有回复"
    kind, chain = results[0]
    assert kind == "chain"
    assert any(isinstance(c, stubs.At) and str(c.qq) == "10086" for c in chain)
    # 排版回归：段首不能是换行，引导语与内容之间的换行要在段内
    joined = "".join(c.text for c in chain if isinstance(c, Plain))
    for c in chain:
        if isinstance(c, Plain):
            assert not c.text.startswith("\n")
    assert "─────\n戳我抽到的圣经" in joined

    # 冷却期内再戳：无输出
    event2 = FakeEvent(raw=raw)
    event2.bot = bot
    results = await run_handler(plugin.on_raw_event(event2))
    assert not results, "冷却期内不应回复"
    print("test_poke_reply_and_cooldown OK")


async def test_poke_ignored_cases():
    plugin = fresh_plugin()
    bot = FakeBot(essence=[])
    # 戳别人：不回
    raw_other = {"post_type": "notice", "notice_type": "notify", "sub_type": "poke",
                 "group_id": 12345, "user_id": 10086, "target_id": 10010}
    e = FakeEvent(raw=raw_other)
    e.bot = bot
    assert not await run_handler(plugin.on_raw_event(e))
    # 撤回通知：不回
    raw_recall = {"post_type": "notice", "notice_type": "group_recall", "group_id": 12345}
    e = FakeEvent(raw=raw_recall)
    e.bot = bot
    assert not await run_handler(plugin.on_raw_event(e))
    # 关闭分群开关：不回
    plugin._settings["12345"] = {"poke": False}
    raw_self = {"post_type": "notice", "notice_type": "notify", "sub_type": "poke",
                "group_id": 12345, "user_id": 10086, "target_id": 88888}
    e = FakeEvent(raw=raw_self)
    e.bot = bot
    assert not await run_handler(plugin.on_raw_event(e))
    print("test_poke_ignored_cases OK")


async def test_draw_merged_uniform():
    """精华与池子合并均匀抽取：两边都要能被抽到。"""
    plugin = fresh_plugin()
    bot = FakeBot(essence=[
        {"sender_id": 1, "sender_nick": "A", "message_id": 1, "time": 0,
         "content": [{"type": "text", "data": {"text": "精华内容"}}]},
    ])
    event = FakeEvent()
    event.bot = bot
    state = main.GroupBibleGachaPlugin._group_state(plugin._pool, "12345")
    state["entries"].append({"id": 1, "text": "池子内容", "images": [], "sender_id": "2", "sender_name": "B", "time": 0, "source": "submit", "key": "k"})
    state["next_id"] = 2
    kinds = set()
    for _ in range(30):
        used, comps, meta, reason = await plugin._draw(event, "12345", "both")
        assert used in ("essence", "pool") and not reason
        kinds.add(used)
    assert kinds == {"essence", "pool"}, f"合并抽取应两边都可能出现：{kinds}"
    # 指定来源仍然生效
    used, _, _, reason = await plugin._draw(event, "12345", "pool")
    assert used == "pool" and not reason
    print("test_draw_merged_uniform OK")


async def test_gacha_essence_forced_refresh():
    """/抽卡 精华 应绕过空结果缓存强制拉取。"""
    plugin = fresh_plugin()
    # 模拟之前缓存了"空精华"
    plugin._essence_cache["12345"] = (time.time(), [])
    bot = FakeBot(essence=[
        {"sender_id": 1, "sender_nick": "A", "message_id": 1, "time": 0,
         "content": [{"type": "text", "data": {"text": "新鲜的精华"}}]},
    ])
    event = FakeEvent()
    event.bot = bot
    event._msg_str = "抽卡 精华"
    results = await run_handler(plugin.gacha(event))
    assert results and results[0][0] == "chain", "强制抽取应成功而非报空"
    texts = "".join(c.text for c in results[0][1] if isinstance(c, Plain))
    assert "新鲜的精华" in texts
    assert any(c[0] == "get_essence_msg_list" for c in bot.calls), "应真实调用精华接口"
    print("test_gacha_essence_forced_refresh OK")


async def test_gacha_unrenderable_placeholder():
    """精华条目内容无法还原时应给占位展示，而不是谎报精华为空。"""
    plugin = fresh_plugin()
    bot = FakeBot(essence=[
        {"sender_id": 10086, "sender_nick": "张三", "message_id": 555, "time": 1761283200,
         "content": None},  # 无内容且 get_msg 拿不到
    ])
    event = FakeEvent()
    event.bot = bot
    event._msg_str = "抽卡 精华"
    results = await run_handler(plugin.gacha(event))
    assert results and results[0][0] == "chain", "有精华但还原失败应展示占位"
    texts = "".join(c.text for c in results[0][1] if isinstance(c, Plain))
    assert "暂时无法还原" in texts
    assert "张三" in texts
    print("test_gacha_unrenderable_placeholder OK")


async def test_preview_layout():
    """/圣经预览 的标题换行要并入首个文本段，避免被 QQ 吞掉。"""
    import main

    plugin = fresh_plugin()
    state = main.GroupBibleGachaPlugin._group_state(plugin._pool, "12345")
    state["entries"].append({"id": 1, "text": "预览内容", "images": [], "sender_id": "2", "sender_name": "李四", "time": 0, "source": "submit", "key": "k"})
    event = FakeEvent()
    event._msg_str = "圣经预览 1"
    results = await run_handler(plugin.preview_entry(event))
    assert results and results[0][0] == "chain"
    chain = results[0][1]
    joined = "".join(c.text for c in chain if isinstance(c, Plain))
    for c in chain:
        if isinstance(c, Plain):
            assert not c.text.startswith("\n")
    assert "🔍 圣经池 #1（李四）：\n预览内容" in joined
    print("test_preview_layout OK")


async def main_async():
    await test_gacha_from_essence()
    await test_gacha_fallback_to_pool()
    await test_gacha_both_empty()
    await test_gacha_get_msg_fallback_for_missing_url()
    await test_draw_merged_uniform()
    await test_gacha_essence_forced_refresh()
    await test_gacha_unrenderable_placeholder()
    await test_submit_direct_to_pool()
    await test_whitelist()
    await test_submit_via_reply_with_image()
    await test_preview_layout()
    await test_poke_reply_and_cooldown()
    await test_poke_ignored_cases()
    print("\nALL ASYNC TESTS PASSED")


if __name__ == "__main__":
    import _test_stubs  # noqa: F401  确保 main 已可用
    from _test_stubs import main  # noqa: F401

    asyncio.run(main_async())
