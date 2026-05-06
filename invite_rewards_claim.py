# Invite Rewards Claim Command
# Add this entire file's content to your main.py

# ============================================================================
# DATABASE SCHEMA UPDATES (Run these in your database)
# ============================================================================
# ALTER TABLE invite_rewards ADD COLUMN IF NOT EXISTS claimed_at TEXT DEFAULT NULL;
# ALTER TABLE invite_rewards ADD COLUMN IF NOT EXISTS claimed_amount BIGINT DEFAULT 0;
# ============================================================================

async def _get_pending_invite_rewards(conn, inviter_id: int) -> list:
    """Get all unclaimed invite rewards for an inviter."""
    rows = await conn.fetch(
        """SELECT invitee_id, reward_amt, wagered_so_far, req_met, claimed_at 
           FROM invite_rewards 
           WHERE inviter_id=$1 AND req_met=TRUE AND (claimed_at IS NULL OR claimed_at='')
           ORDER BY rewarded_at ASC""",
        str(inviter_id)
    )
    return rows

async def _get_claimed_invite_rewards(conn, inviter_id: int) -> tuple:
    """Get count and total amount of claimed rewards."""
    row = await conn.fetchrow(
        """SELECT COUNT(*) as claim_count, COALESCE(SUM(claimed_amount), 0) as total_claimed
           FROM invite_rewards
           WHERE inviter_id=$1 AND claimed_at IS NOT NULL AND claimed_at != ''""",
        str(inviter_id)
    )
    if row:
        return row["claim_count"], row["total_claimed"]
    return 0, 0

async def _get_wager_requirement_progress(conn, inviter_id: int) -> dict:
    """Get wager requirement progress for inviter."""
    row = await conn.fetchrow(
        """SELECT required_amt, wagered_so_far, req_met
           FROM wager_requirements
           WHERE user_id=$1""",
        str(inviter_id)
    )
    if row:
        return {
            "required": row["required_amt"],
            "wagered": row["wagered_so_far"],
            "met": row["req_met"]
        }
    return {"required": 0, "wagered": 0, "met": False}

@bot.tree.command(name="claiminviterewards", description="View and claim your invite rewards")
async def cmd_claiminviterewards(interaction: discord.Interaction):
    """Claim pending invite rewards and view reward summary."""
    await interaction.response.defer()
    
    conn = await get_conn()
    try:
        await ensure_user(conn, interaction.user)
        
        # Get pending rewards
        pending_rewards = await _get_pending_invite_rewards(conn, interaction.user.id)
        
        # Get claimed rewards summary
        claim_count, total_claimed = await _get_claimed_invite_rewards(conn, interaction.user.id)
        
        # Get wager requirement
        wager_info = await _get_wager_requirement_progress(conn, interaction.user.id)
        
        # Get user balance
        user_row = await get_user(conn, interaction.user.id)
        current_balance = user_row["balance"] if user_row else 0
        
        # Get user avatar
        avatar_url = await get_avatar(interaction.user)
        
        # Build embed
        embed = discord.Embed(
            title="🎁 INVITE REWARDS",
            color=C_GOLD,
            description=""
        )
        
        # Claimed section
        embed.add_field(
            name="📊 CLAIMED",
            value=f"{claim_count} invites claimed\n{_money(total_claimed)}",
            inline=False
        )
        
        # Pending section
        pending_count = len(pending_rewards)
        pending_total = sum(r["reward_amt"] for r in pending_rewards)
        embed.add_field(
            name="⏳ PENDING",
            value=f"{pending_count} awaiting claim\n{_money(pending_total)}",
            inline=False
        )
        
        # Wager requirement section
        req_total = wager_info["required"]
        req_wagered = wager_info["wagered"]
        req_met = wager_info["met"]
        req_remaining = max(0, req_total - req_wagered)
        
        if req_total > 0:
            bar_fill = int((req_wagered / req_total) * 12) if req_total > 0 else 0
            progress = progress_bar(req_wagered, req_total)
            
            status = "🟢 COMPLETE" if req_met else "🎮 IN PROGRESS"
            embed.add_field(
                name="🎲 WAGER REQUIREMENT",
                value=f"{status}\n{format_amount(req_wagered)} / {format_amount(req_total)}\n{progress}\n{format_amount(req_remaining)} remaining",
                inline=False
            )
        else:
            embed.add_field(
                name="🎲 WAGER REQUIREMENT",
                value="No active requirement",
                inline=False
            )
        
        # Balance section
        embed.add_field(
            name="💰 BALANCE",
            value=f"{_money(current_balance)} current",
            inline=False
        )
        
        embed.set_thumbnail(url=avatar_url)
        _brand_embed(embed)
        
        # Create view with claim button
        class ClaimView(discord.ui.View):
            def __init__(self, user_id: int, pending: list, pending_total: int):
                super().__init__(timeout=60)
                self.user_id = user_id
                self.pending = pending
                self.pending_total = pending_total
                
                # Disable button if no pending rewards
                if len(pending) == 0:
                    self.claim_btn.disabled = True
                    self.claim_btn.label = "No Rewards to Claim"
            
            @discord.ui.button(label=f"Claim {format_amount(pending_total)}", style=discord.ButtonStyle.green)
            async def claim_btn(self, btn_interaction: discord.Interaction, button: discord.ui.Button):
                # Verify user
                if btn_interaction.user.id != self.user_id:
                    await btn_interaction.response.send_message(
                        embed=discord.Embed(
                            color=C_LOSS,
                            description="❌ You can only claim your own rewards."
                        ),
                        ephemeral=True
                    )
                    return
                
                await btn_interaction.response.defer()
                
                conn2 = await get_conn()
                try:
                    total_claimed = 0
                    claimed_ids = []
                    
                    # Process each pending reward
                    for reward in self.pending:
                        invitee_id = reward["invitee_id"]
                        reward_amt = reward["reward_amt"]
                        
                        # Check inviter still exists
                        inviter = await get_user(conn2, self.user_id)
                        if not inviter:
                            continue
                        
                        # Check if suspended
                        suspended = await conn2.fetchrow(
                            "SELECT * FROM suspended_invite_rewards WHERE user_id=$1",
                            str(self.user_id)
                        )
                        if suspended:
                            continue
                        
                        # Credit balance
                        await update_balance(conn2, self.user_id, reward_amt)
                        
                        # Mark as claimed
                        await conn2.execute(
                            """UPDATE invite_rewards 
                               SET claimed_at=$1, claimed_amount=$2 
                               WHERE invitee_id=$3""",
                            now_ts(), reward_amt, invitee_id
                        )
                        
                        # Log transaction
                        await log_transaction(
                            conn2, self.user_id, "invite_reward_claim", reward_amt,
                            f"Claimed reward from invitee {invitee_id}"
                        )
                        
                        total_claimed += reward_amt
                        claimed_ids.append(invitee_id)
                    
                    # Send success embed
                    success_embed = discord.Embed(
                        title="✅ REWARDS CLAIMED",
                        color=C_WIN,
                        description=f""
                    )
                    success_embed.add_field(
                        name="📦 Claimed",
                        value=f"{len(claimed_ids)} reward(s)\n{_money(total_claimed)}",
                        inline=False
                    )
                    success_embed.add_field(
                        name="💎 New Balance",
                        value=_money(inviter["balance"] + total_claimed),
                        inline=False
                    )
                    _brand_embed(success_embed)
                    
                    # Send to reward log if configured
                    if REWARD_LOG_ID:
                        try:
                            reward_channel = bot.get_channel(REWARD_LOG_ID)
                            if reward_channel:
                                log_embed = discord.Embed(
                                    title="🎁 Invite Reward Claimed",
                                    color=C_GOLD,
                                    description=f"<@{self.user_id}> claimed {len(claimed_ids)} invite reward(s)"
                                )
                                log_embed.add_field(
                                    name="Amount",
                                    value=_money(total_claimed),
                                    inline=True
                                )
                                log_embed.add_field(
                                    name="Timestamp",
                                    value=now_ts(),
                                    inline=True
                                )
                                _brand_embed(log_embed)
                                await reward_channel.send(embed=log_embed)
                        except Exception as e:
                            print(f"[INVITE] Failed to send reward log: {e}")
                    
                    await btn_interaction.followup.send(embed=success_embed, ephemeral=True)
                    
                except Exception as e:
                    print(f"[INVITE] Claim error: {e}")
                    error_embed = discord.Embed(
                        color=C_LOSS,
                        description=f"❌ Claim failed: {str(e)[:100]}"
                    )
                    await btn_interaction.followup.send(embed=error_embed, ephemeral=True)
                finally:
                    await release_conn(conn2)
        
        view = ClaimView(interaction.user.id, pending_rewards, pending_total)
        await interaction.followup.send(embed=embed, view=view)
        
    except Exception as e:
        print(f"[INVITE] Command error: {e}")
        error_embed = discord.Embed(
            color=C_LOSS,
            description=f"❌ Error: {str(e)[:100]}"
        )
        await interaction.followup.send(embed=error_embed, ephemeral=True)
    finally:
        await release_conn(conn)
