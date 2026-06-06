import os
import pickle
import socket
import time

with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
    sock.bind(("localhost", 8818))

    print("Waiting for messages")

    anchors = {}

    while True:  # @done player leaves an anchor
        data, addr = sock.recvfrom(1024)
        if not data:
            break

        _ = pickle.loads(data)
        anchor_id, overlaps, guid, delta, o, state, health, stamina, name, seen = _

        if anchor_id not in anchors:
            anchors[anchor_id] = {
                guid: (delta, o, state, health, stamina, name, seen)
            }

        for anchor in list(anchors.keys()):
            for person in list(anchors[anchor].keys()):
                last_seen = anchors[anchor][person][-1]
                if last_seen + 5 < int(time.time()):
                    anchors[anchor].pop(person)

        anchors[anchor_id][guid] = (delta, o, state, health, stamina, name, seen)
        for e in set([anchor_id, *overlaps]):
            if e not in anchors:
                continue
            
            for member in anchors[e]:
                if guid == member: # don't notify sender of their own overlap
                    continue
                
                sock.sendto(
                    pickle.dumps([e, member, *anchors[e][member]]), addr
                )

        sock.sendto(b"", addr)  # empty/terminator byte
