# void_api.py — FastAPI Wrapper for VOID Erotic AI
# The parasitic layer: VOID state machine gates and modulates LLM generation.
# No fine-tuning. No retraining. Pure topological control.

import uuid
import json
from typing import Optional
from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel

from void_state import VoidSession, VoidObserver, BodyTopology
from void_prompt import generate_system_prompt, generate_api_params
from void_llm import VoidLLM
from config import get_topology, BUDGET_PRESETS, TOPOLOGIES


# === APP ===

app = FastAPI(
    title="VOID Erotic AI",
    description="Topology-gated erotic AI. Every act of knowing costs something.",
    version="0.1.0",
)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_methods=["*"],
    allow_headers=["*"],
)

# In-memory stores (swap for Redis/DB in production)
sessions: dict[str, VoidSession] = {}
llm_clients: dict[str, VoidLLM] = {}


# === REQUEST/RESPONSE MODELS ===

class SessionCreate(BaseModel):
    topology: str = "default"
    budget: int = 15
    custom_zones: Optional[list[tuple[str, str]]] = None
    provider: str = "mock"  # "anthropic", "openai", "mock"
    model: Optional[str] = None
    api_key: Optional[str] = None

class InteractRequest(BaseModel):
    zone: str

class ChatRequest(BaseModel):
    message: str
    zone: Optional[str] = None

class RecoveryRequest(BaseModel):
    ticks: int = 3

class SessionResponse(BaseModel):
    session_id: str
    state: dict
    system_prompt: str
    api_params: dict

class InteractResponse(BaseModel):
    interaction: dict
    state: dict
    system_prompt: str
    api_params: dict

class RecoveryResponse(BaseModel):
    recovery: dict
    state: dict
    system_prompt: str
    api_params: dict


# === ENDPOINTS ===

@app.get("/")
def root():
    return {
        "name": "VOID Erotic AI",
        "version": "0.1.0",
        "philosophy": "Every act of knowing costs something. Every passage leaves a mark.",
        "endpoints": {
            "POST /session/start": "Create a new session",
            "POST /session/{id}/interact": "Interact with a zone",
            "POST /session/{id}/recovery": "Recovery phase",
            "GET /session/{id}/state": "Get current state + prompt",
            "GET /session/{id}/prompt": "Get system prompt only",
            "GET /topologies": "List available body topologies",
            "GET /budgets": "List budget presets",
        }
    }


@app.post("/session/start", response_model=SessionResponse)
def start_session(req: SessionCreate):
    """
    Create a new VOID session.

    Choose a topology (body configuration) and budget (session length).
    The session starts at 'surface' — all passages are potential.
    """
    session_id = str(uuid.uuid4())[:8]

    # Build topology
    if req.custom_zones:
        from config import topology_shapeshifter
        body = topology_shapeshifter(req.custom_zones)
    else:
        body = get_topology(req.topology)

    # Create session
    session = VoidSession(
        observer=VoidObserver(budget=req.budget),
        body=body,
    )
    sessions[session_id] = session

    # Create LLM client
    model = req.model
    if not model:
        model = {
            "anthropic": "claude-sonnet-4-5-20250929",
            "openai": "gpt-4o",
            "ollama": "mistral-nemo",
            "mock": "mock",
        }.get(req.provider, "mock")

    llm_clients[session_id] = VoidLLM(
        session=session,
        provider=req.provider,
        model=model,
        api_key=req.api_key,
    )

    return SessionResponse(
        session_id=session_id,
        state=session.state_snapshot(),
        system_prompt=generate_system_prompt(session),
        api_params=generate_api_params(session),
    )


@app.post("/session/{session_id}/interact", response_model=InteractResponse)
def interact(session_id: str, req: InteractRequest):
    """
    One interaction tick.

    Move toward a zone. The DDF engine handles everything:
    - Bridge found → decay stability, tick budget, accumulate heat
    - No bridge → fold space (expensive) or wormhole (desperate)
    - Budget depleted → frozen. Session over.

    Returns updated state + new system prompt for LLM generation.
    """
    session = sessions.get(session_id)
    if not session:
        raise HTTPException(404, f"Session {session_id} not found")

    if session.observer.is_frozen:
        raise HTTPException(
            409,
            "Observer is frozen. Budget depleted. "
            "Use /session/{id}/recovery or start a new session."
        )

    result = session.interact(req.zone)

    return InteractResponse(
        interaction=result,
        state=session.state_snapshot(),
        system_prompt=generate_system_prompt(session),
        api_params=generate_api_params(session),
    )


@app.post("/session/{session_id}/chat")
def chat(session_id: str, req: ChatRequest):
    """
    Full conversational turn: message + optional zone movement → LLM response.

    This is the main endpoint. Send a message, optionally move to a zone.
    The VOID engine modulates everything: prompt, temperature, token limit.
    The LLM speaks through the topology.
    """
    llm = llm_clients.get(session_id)
    if not llm:
        raise HTTPException(404, f"Session {session_id} not found")

    session = sessions.get(session_id)
    if session and session.observer.is_frozen:
        raise HTTPException(
            409,
            "Observer is frozen. Budget depleted. "
            "Use /session/{id}/recovery or start a new session."
        )

    result = llm.chat(req.message, zone=req.zone)

    return {
        "response": result["response"],
        "interaction": result["interaction"],
        "state": result["state"],
        "api_params": result["api_params"],
    }


@app.post("/session/{session_id}/recovery", response_model=RecoveryResponse)
def recovery(session_id: str, req: RecoveryRequest):
    """
    Recovery phase.

    Budget partially restores. Heat stays (you don't forget).
    Bridges partially recover. Dimensions may re-expand.

    This is the pause — the breath between rounds.
    """
    session = sessions.get(session_id)
    if not session:
        raise HTTPException(404, f"Session {session_id} not found")

    result = session.recovery(req.ticks)

    return RecoveryResponse(
        recovery=result,
        state=session.state_snapshot(),
        system_prompt=generate_system_prompt(session),
        api_params=generate_api_params(session),
    )


@app.get("/session/{session_id}/state")
def get_state(session_id: str):
    """Full session state + system prompt + API parameters."""
    session = sessions.get(session_id)
    if not session:
        raise HTTPException(404, f"Session {session_id} not found")

    return {
        "state": session.state_snapshot(),
        "system_prompt": generate_system_prompt(session),
        "api_params": generate_api_params(session),
    }


@app.get("/session/{session_id}/prompt")
def get_prompt(session_id: str):
    """System prompt only — for direct injection into LLM calls."""
    session = sessions.get(session_id)
    if not session:
        raise HTTPException(404, f"Session {session_id} not found")

    return {
        "system_prompt": generate_system_prompt(session),
        "api_params": generate_api_params(session),
    }


@app.get("/topologies")
def list_topologies():
    """Available body topologies."""
    result = {}
    for name, factory in TOPOLOGIES.items():
        topo = factory()
        result[name] = {
            "bridges": [
                {"zone1": b.zone1, "zone2": b.zone2,
                 "stability": b.stability.value}
                for b in topo.bridges.values()
            ],
            "fold_energy": topo.fold_energy,
        }
    return result


@app.get("/budgets")
def list_budgets():
    """Budget presets with descriptions."""
    return {
        name: {
            "budget": val,
            "description": {
                "quickie": "Fast, intense, collapses quickly",
                "standard": "Normal session",
                "marathon": "Long, evolving encounter",
                "tantric": "Slow burn, high dimensionality throughout",
                "edging": "Short budget with recovery cycles",
            }.get(name, ""),
        }
        for name, val in BUDGET_PRESETS.items()
    }


# === RUN ===

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8069)
