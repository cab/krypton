// Krypton JS runtime — actor stubs (not supported on JS target)

function unsupported() {
  throw new Error('Actors are not supported on the JS target');
}

export function raw_spawn(_f) { unsupported(); }
export function raw_send(_target, _msg) { unsupported(); }
export function raw_receive(_mb) { unsupported(); }
export function raw_receive_timeout(_mb, _ms) { unsupported(); }
export function raw_actor_ref(_mb) { unsupported(); }
export function raw_mailbox_size(_mb) { unsupported(); }
export function raw_create_mailbox() { unsupported(); }
export function raw_adapter(_target, _wrapper) { unsupported(); }
export function raw_ask(_target, _wrapper, _timeout) { unsupported(); }
