import os
import pickle
import socket


with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
    sock.bind(("localhost", 8818))

    print("Waiting for messages")

    anchors = {}

    while True:
        data, addr = sock.recvfrom(1024)
        if not data:
            break

        _ = pickle.loads(data)
        anchor_id, player, delta, o, state, health, stamina = _
        if anchor_id not in anchors:
            anchors[anchor_id] = {player: (delta, o, state, health, stamina)}

        anchors[anchor_id][player] = (delta, o, state, health, stamina)
        
        for member in anchors[anchor_id]:
            sock.sendto(
                pickle.dumps([anchor_id, member, *anchors[anchor_id][member]]),
                addr
            )

        sock.sendto(b"", addr) # empty/terminator byte
