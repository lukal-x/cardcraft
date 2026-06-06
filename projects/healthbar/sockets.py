import os
import pickle
import socket
import time

with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
    sock.bind(("localhost", 8818))

    print("Waiting for messages")

    anchors = {}

    while True:  # @todo player leaves an anchor
        data, addr = sock.recvfrom(1024)
        if not data:
            break

        _ = pickle.loads(data)
        anchor_id, player, delta, o, state, health, stamina, guid, seen = _

        if anchor_id not in anchors:
            anchors[anchor_id] = {
                player: (delta, o, state, health, stamina, guid, seen)
            }

        for anchor in list(anchors.keys()):
            for person in list(anchors[anchor].keys()):
                last_seen = anchors[anchor][person][-1]
                if last_seen + 5 < int(time.time()):
                    anchors[anchor].pop(person)

        anchors[anchor_id][player] = (delta, o, state, health, stamina, guid, seen)
        for member in anchors[anchor_id]:
            sock.sendto(
                pickle.dumps([anchor_id, member, *anchors[anchor_id][member]]), addr
            )

        sock.sendto(b"", addr)  # empty/terminator byte
