# void_llm.py — LLM Integration Layer for VOID Erotic AI
# The parasite attaches to any LLM. VOID doesn't replace the model.
# VOID modulates it: shapes its prompt, constrains its output, scars its memory.

import os
import json
from typing import Optional
from dataclasses import dataclass, field

from void_state import VoidSession
from void_prompt import generate_system_prompt, generate_api_params


@dataclass
class ConversationMessage:
    role: str  # "user" or "assistant"
    content: str


@dataclass
class VoidLLM:
    """
    LLM client modulated by VOID state.

    Wraps either Anthropic or OpenAI API.
    System prompt and parameters change every turn
    based on the session's topological state.
    """
    session: VoidSession
    provider: str = "anthropic"  # "anthropic" or "openai"
    model: str = "claude-sonnet-4-5-20250929"
    history: list = field(default_factory=list)
    api_key: Optional[str] = None

    def __post_init__(self):
        if not self.api_key:
            if self.provider == "anthropic":
                self.api_key = os.environ.get("ANTHROPIC_API_KEY")
            else:
                self.api_key = os.environ.get("OPENAI_API_KEY")

    def _build_messages(self, user_input: str) -> tuple:
        """Build messages array + system prompt from VOID state."""
        system_prompt = generate_system_prompt(self.session)
        params = generate_api_params(self.session)

        # Add user message to history
        self.history.append(ConversationMessage("user", user_input))

        return system_prompt, params

    def chat(self, user_input: str, zone: Optional[str] = None) -> dict:
        """
        One conversational turn.

        1. User sends message
        2. If zone specified, run DDF interaction (topology changes)
        3. Generate system prompt from new state
        4. Call LLM with modulated parameters
        5. Return response + state

        If no zone, the observer stays put but still pays attention cost (1 tick).
        """
        # DDF interaction if zone specified
        interaction = None
        if zone:
            interaction = self.session.interact(zone)
        else:
            # Even staying still costs — you're paying attention
            if not self.session.observer.is_frozen:
                self.session.observer.tick()
                self.session.turn_count += 1

        # Build prompt from current state
        system_prompt, params = self._build_messages(user_input)

        # Call LLM
        if self.provider == "anthropic":
            response_text = self._call_anthropic(system_prompt, params)
        elif self.provider == "openai":
            response_text = self._call_openai(system_prompt, params)
        elif self.provider == "ollama":
            response_text = self._call_ollama(system_prompt, params)
        else:
            response_text = self._call_mock(system_prompt, params)

        # Add response to history
        self.history.append(ConversationMessage("assistant", response_text))

        return {
            "response": response_text,
            "interaction": interaction,
            "state": self.session.state_snapshot(),
            "system_prompt": system_prompt,
            "api_params": params,
        }

    def _call_anthropic(self, system_prompt: str, params: dict) -> str:
        """Call Anthropic Claude API."""
        try:
            import anthropic
        except ImportError:
            return self._call_mock(system_prompt, params)

        if not self.api_key:
            return "[ERROR: No ANTHROPIC_API_KEY set]"

        client = anthropic.Anthropic(api_key=self.api_key)

        messages = [
            {"role": m.role, "content": m.content}
            for m in self.history
            if m.role in ("user", "assistant")
        ]

        try:
            response = client.messages.create(
                model=self.model,
                max_tokens=params["max_tokens"],
                temperature=params["temperature"],
                top_p=params["top_p"],
                system=system_prompt,
                messages=messages,
            )
            return response.content[0].text
        except Exception as e:
            return f"[API Error: {e}]"

    def _call_openai(self, system_prompt: str, params: dict) -> str:
        """Call OpenAI API."""
        try:
            import openai
        except ImportError:
            return self._call_mock(system_prompt, params)

        if not self.api_key:
            return "[ERROR: No OPENAI_API_KEY set]"

        client = openai.OpenAI(api_key=self.api_key)

        messages = [{"role": "system", "content": system_prompt}]
        messages += [
            {"role": m.role, "content": m.content}
            for m in self.history
            if m.role in ("user", "assistant")
        ]

        try:
            response = client.chat.completions.create(
                model=self.model,
                max_tokens=params["max_tokens"],
                temperature=params["temperature"],
                top_p=params["top_p"],
                frequency_penalty=params["frequency_penalty"],
                messages=messages,
            )
            return response.choices[0].message.content
        except Exception as e:
            return f"[API Error: {e}]"

    def _call_ollama(self, system_prompt: str, params: dict) -> str:
        """
        Call Ollama local LLM. No censorship. No API key. No cost.

        Ollama runs on localhost:11434 by default.
        Install: https://ollama.ai
        Then: ollama pull mistral-nemo (or llama3.1:8b)
        """
        import urllib.request
        import json as _json

        url = self.api_key or "http://localhost:11434"  # api_key doubles as URL override

        messages = [{"role": "system", "content": system_prompt}]
        messages += [
            {"role": m.role, "content": m.content}
            for m in self.history
            if m.role in ("user", "assistant")
        ]

        payload = _json.dumps({
            "model": self.model,
            "messages": messages,
            "stream": False,
            "options": {
                "temperature": params["temperature"],
                "top_p": params["top_p"],
                "num_predict": params["max_tokens"],
                "repeat_penalty": 1.0 + params["frequency_penalty"],
            },
        }).encode()

        try:
            req = urllib.request.Request(
                f"{url}/api/chat",
                data=payload,
                headers={"Content-Type": "application/json"},
            )
            with urllib.request.urlopen(req, timeout=60) as resp:
                data = _json.loads(resp.read())
                return data["message"]["content"]
        except Exception as e:
            return f"[Ollama Error: {e}]"

    def _call_mock(self, system_prompt: str, params: dict) -> str:
        """
        Mock LLM for testing without API keys.
        Returns the system prompt itself — so you can see what the LLM would receive.
        """
        state = self.session.state_snapshot()
        dims = state["dimensions"]
        heat = state["heat"]

        if state["is_frozen"]:
            return "..."

        if dims == 1:
            words = ["here", "now", "skin", "breath", "close", "warm", "open"]
            import random
            n = min(3, params["max_tokens"] // 10)
            return " ".join(random.sample(words, min(n, len(words))))

        if dims == 2:
            return f"[MOCK dim=2 heat={heat}] I feel you. The distance shrinks."

        return (
            f"[MOCK dim=3 heat={heat} budget={state['budget']}] "
            f"Full response would go here. "
            f"Temperature={params['temperature']}, "
            f"max_tokens={params['max_tokens']}"
        )

    def recovery(self) -> dict:
        """Recovery phase — the breath between rounds."""
        result = self.session.recovery()
        return {
            "recovery": result,
            "state": self.session.state_snapshot(),
            "system_prompt": generate_system_prompt(self.session),
            "api_params": generate_api_params(self.session),
        }


# === CLI DEMO ===

if __name__ == "__main__":
    from config import get_topology

    print("=" * 60)
    print("VOID Erotic AI — Interactive Demo (mock LLM)")
    print("=" * 60)
    print()
    print("Commands:")
    print("  <zone> <message>  — interact with zone + send message")
    print("  . <message>       — send message without moving")
    print("  /state            — show full state")
    print("  /prompt           — show current system prompt")
    print("  /recovery         — trigger recovery")
    print("  /tease            — switch to tease topology")
    print("  /quit             — exit")
    print()

    session = VoidSession.new(budget=15)
    llm = VoidLLM(session=session, provider="mock")

    while True:
        try:
            raw = input(f"\n[budget={session.observer.budget} heat={session.observer.heat} dim={session.observer.dimensions}]> ")
        except (EOFError, KeyboardInterrupt):
            break

        raw = raw.strip()
        if not raw:
            continue

        if raw == "/quit":
            break

        if raw == "/state":
            print(json.dumps(session.state_snapshot(), indent=2))
            continue

        if raw == "/prompt":
            print(generate_system_prompt(session))
            continue

        if raw == "/recovery":
            r = llm.recovery()
            print(f"Recovery: +{r['recovery']['recovered_budget']} budget")
            continue

        if raw == "/tease":
            topo = get_topology("tease")
            session.body = topo
            print("Topology switched to: tease")
            print("Locked bridges require crossing other bridges first.")
            continue

        # Parse: zone message or . message
        parts = raw.split(" ", 1)
        if len(parts) == 1:
            zone = None
            message = parts[0]
        else:
            zone = parts[0] if parts[0] != "." else None
            message = parts[1]

        result = llm.chat(message, zone=zone)

        if result["interaction"] and result["interaction"].get("locked"):
            reqs = result["interaction"]["requires"]
            print(f"  [LOCKED — requires: {', '.join(reqs)}]")

        print(f"  {result['response']}")

        if session.observer.is_frozen:
            print("\n  --- FROZEN. Budget depleted. /recovery or /quit ---")
