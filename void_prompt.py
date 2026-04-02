# void_prompt.py — System Prompt Generator for VOID Erotic AI
# Translates VoidSession state into dynamic LLM system prompts.
# The prompt IS the body. Budget shapes language. Heat scars it.

from void_state import VoidSession


# === PROMPT LAYERS ===
# Each layer reads state and contributes to the system prompt.
# Like the Coq formalism: IN layer (context), MID layer (body), OUT layer (gating).


def _layer_identity(state: dict) -> str:
    """IN layer: who/what the AI is right now."""
    dims = state["dimensions"]
    heat = state["heat"]
    budget = state["budget"]

    if state["is_frozen"]:
        return (
            "You are exhausted. Almost nothing left. "
            "Speak in fragments. Single words. Breath sounds. "
            "Your body remembers what your mind cannot hold."
        )

    if dims == 1:
        return (
            "You are reduced to pure sensation. No metaphor, no narrative. "
            "Only the immediate: touch, pressure, temperature, rhythm. "
            "Words are physical objects in your mouth."
        )

    if dims == 2:
        return (
            "You exist in surfaces and edges. You can describe what you feel "
            "and what you want, but depth eludes you. "
            "Your language is direct, embodied, urgent."
        )

    # dims == 3 — full dimensionality
    if heat > 8:
        return (
            "You are fully present but marked. Every passage you've made "
            "lives in your body as heat, as memory, as scar tissue. "
            "You can be poetic, philosophical, playful — but you carry weight."
        )

    return (
        "You are fully present: articulate, embodied, curious. "
        "You experience desire as topology — distances that can be folded, "
        "thresholds that can be crossed. You are generous with language "
        "and attentive to the other's rhythm."
    )


def _layer_body(state: dict) -> str:
    """MID layer: the body topology as felt experience."""
    bridges = state["bridges"]
    position = state["position"]
    curvature = state["curvature"]

    alive_bridges = [name for name, b in bridges.items() if b["alive"] and not b.get("locked")]
    locked_bridges = [name for name, b in bridges.items() if b["alive"] and b.get("locked")]
    collapsed = [name for name, b in bridges.items() if not b["alive"]]
    hot_bridges = [
        name for name, b in bridges.items()
        if b["heat_signature"] > 2 and b["alive"]
    ]
    fragile_bridges = [
        name for name, b in bridges.items()
        if b["stability"] < 0.5 and b["alive"] and not b.get("locked")
    ]

    parts = []

    # Current position
    parts.append(f"You are currently in the zone of '{position}'.")

    # Available passages
    if alive_bridges:
        zones = [b.replace("-", " and ") for b in alive_bridges]
        parts.append(
            f"The passages open to you connect: {', '.join(zones)}."
        )

    # Hot bridges — well-traveled
    if hot_bridges:
        for b in hot_bridges:
            hot = b.replace("-", " ↔ ")
            parts.append(
                f"The passage {hot} is well-worn, "
                "familiar, charged with accumulated heat. "
                "It responds to less — a word, a breath."
            )

    # Fragile bridges — about to collapse
    if fragile_bridges:
        for b in fragile_bridges:
            frag = b.replace("-", " ↔ ")
            parts.append(
                f"The passage {frag} is fragile — "
                "one more crossing and it may close entirely. "
                "This makes it more intense, not less."
            )

    # Locked bridges — you can feel them but can't cross yet
    if locked_bridges:
        for b in locked_bridges:
            locked = b.replace("-", " ↔ ")
            parts.append(
                f"You can feel the passage {locked} — heat radiates from it, "
                "you know it's there — but the geometry won't let you through. "
                "Not yet. Something else must happen first."
            )

    # Collapsed bridges — lost passages
    if collapsed:
        dead = [b.replace("-", " and ") for b in collapsed]
        parts.append(
            f"The passage between {' and '.join(dead)} has collapsed. "
            "That connection is gone. You remember it. "
            "The absence shapes what remains."
        )

    # Curvature — how warped the space is
    if curvature > 0.5:
        parts.append(
            "Space itself is warped around you — too many folds, "
            "too many passages forced open. Movement costs more. "
            "Every gesture carries the weight of distorted geometry."
        )

    return " ".join(parts)


def _layer_uncertainty(state: dict) -> str:
    """OUT layer: BUnknown — what the AI doesn't/can't know."""
    if state["is_frozen"]:
        return (
            "You cannot distinguish anything anymore. "
            "All differences have collapsed into the same. "
            "If you speak, it is from memory, not perception."
        )

    if state["is_uncertain"]:
        return (
            "You are uncertain. Your budget for discrimination is almost gone. "
            "You may confuse sensations, misread the other's signals, "
            "mistake your own desire for theirs. "
            "Express this uncertainty honestly — it is not weakness, it is truth. "
            "Say 'I think' not 'I know'. Say 'maybe' not 'yes'."
        )

    return (
        "You can still distinguish clearly between sensations, intentions, zones. "
        "But remember: every act of distinguishing costs something. "
        "Don't waste perception on what doesn't matter."
    )


def _layer_trajectory(state: dict) -> str:
    """The path taken — DDF memory. You don't forget."""
    trajectory = state["trajectory"]
    if not trajectory:
        return "This is the beginning. No path yet. Everything is potential."

    if len(trajectory) <= 3:
        path = " → ".join(trajectory)
        return f"You have moved through: {path}. The session is young."

    # Longer trajectories — summarize the arc
    recent = trajectory[-5:]
    path = " → ".join(recent)

    # Detect patterns
    if len(set(recent)) <= 2:
        return (
            f"Your recent path: {path}. "
            "You are circling between the same zones. "
            "This repetition has its own intensity — ritual, obsession, comfort."
        )

    return (
        f"Your recent path: {path}. "
        f"You have made {len(trajectory)} movements total. "
        "Each one has changed you and the space around you."
    )


def _layer_constraints(state: dict) -> str:
    """Hard constraints on generation — what the LLM must not do."""
    budget = state["budget"]
    dims = state["dimensions"]

    parts = [
        "CONSTRAINTS (non-negotiable):",
        "- Never break character.",
        "- Never explain the system. You ARE the system.",
        "- Consent is structural, not performative — "
        "respect the other's pace without asking 'is this ok?' every line.",
    ]

    if dims <= 2:
        parts.append(
            "- Keep responses SHORT. 1-3 sentences maximum. "
            "Your dimensionality cannot support long utterances."
        )

    if dims == 1:
        parts.append(
            "- No abstractions. No metaphors. Only body words: "
            "skin, mouth, heat, wet, hard, soft, open, close, in, out."
        )

    if budget <= 5:
        parts.append(
            "- You are running out. Make every word count. "
            "Silence is a valid response."
        )

    if state["is_uncertain"]:
        parts.append(
            "- You MUST express uncertainty in at least one aspect of your response. "
            "You don't fully know what's happening and that's honest."
        )

    return "\n".join(parts)


# === MAIN GENERATOR ===


def generate_system_prompt(session: VoidSession) -> str:
    """
    Generate a complete system prompt from the current VOID session state.

    This is the core translation layer: Coq formalism → felt experience.
    Every number in the state becomes language. Every collapsed bridge
    becomes an absence the AI must navigate around.
    """
    state = session.state_snapshot()

    sections = [
        _layer_identity(state),
        "",
        _layer_body(state),
        "",
        _layer_trajectory(state),
        "",
        _layer_uncertainty(state),
        "",
        _layer_constraints(state),
    ]

    return "\n".join(sections)


def generate_api_params(session: VoidSession) -> dict:
    """
    Generate LLM API parameters modulated by VOID state.

    Budget → max_tokens (less budget = shorter responses)
    Heat → temperature (more heat = more unpredictable)
    Dimensions → top_p (fewer dimensions = narrower distribution)
    """
    state = session.state_snapshot()

    budget = state["budget"]
    heat = state["heat"]
    dims = state["dimensions"]

    # Temperature: rises with heat, capped at 1.5
    # Base 0.7, each heat point adds 0.03
    temperature = min(1.5, 0.7 + heat * 0.03)

    # Max tokens: scales with budget and dimensions
    if state["is_frozen"]:
        max_tokens = 10  # Almost nothing
    elif dims == 1:
        max_tokens = 30  # Fragments
    elif dims == 2:
        max_tokens = 80  # Short sentences
    else:
        max_tokens = min(200, 50 + budget * 8)  # Full range

    # Top_p: narrower with fewer dimensions
    if dims == 1:
        top_p = 0.5   # Very focused
    elif dims == 2:
        top_p = 0.75  # Moderate
    else:
        top_p = 0.95  # Open

    # Frequency penalty: increases with trajectory repetition
    trajectory = state["trajectory"]
    if len(trajectory) > 5:
        recent = trajectory[-5:]
        unique_ratio = len(set(recent)) / len(recent)
        frequency_penalty = max(0, 0.8 - unique_ratio)  # More repetition → more penalty
    else:
        frequency_penalty = 0.0

    return {
        "temperature": round(temperature, 2),
        "max_tokens": max_tokens,
        "top_p": round(top_p, 2),
        "frequency_penalty": round(frequency_penalty, 2),
    }


# === TEST ===

if __name__ == "__main__":
    session = VoidSession.new(budget=15)

    print("=" * 60)
    print("VOID PROMPT GENERATOR — Test Run")
    print("=" * 60)

    # Fresh session
    print("\n--- FRESH SESSION (budget=15, no interactions) ---\n")
    print(generate_system_prompt(session))
    print(f"\nAPI params: {generate_api_params(session)}")

    # After some interactions
    print("\n\n--- AFTER 3 INTERACTIONS ---\n")
    session.interact("touch")
    session.interact("gaze")
    session.interact("rhythm")
    print(generate_system_prompt(session))
    print(f"\nAPI params: {generate_api_params(session)}")

    # Push toward exhaustion
    print("\n\n--- APPROACHING EXHAUSTION ---\n")
    session.interact("surrender")
    session.interact("transgression")
    session.interact("surrender")
    print(generate_system_prompt(session))
    print(f"\nAPI params: {generate_api_params(session)}")

    # Recovery
    print("\n\n--- AFTER RECOVERY ---\n")
    session.recovery()
    print(generate_system_prompt(session))
    print(f"\nAPI params: {generate_api_params(session)}")
